{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Network.Wai.WebSockets where

import Network.Wai
import Control.Exception (Exception, throwIO, assert)
import Control.Applicative ((<$>))
import Control.Monad (when, unless)
import Data.Typeable (Typeable)
import Blaze.ByteString.Builder
import Data.Monoid ((<>), mempty)
import qualified Crypto.Hash.SHA1 as SHA1
import Data.Word (Word8, Word32, Word64)
import Data.ByteString (ByteString)
import Data.Bits ((.|.), testBit, clearBit, shiftL, (.&.), Bits, xor, shiftR)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import qualified Data.ByteString as S
import qualified Data.ByteString.Base64 as B64
import Data.IORef


type IsText = Bool

data Connection = Connection
    { connSend :: IsText -> ByteString -> IO ()
    , connRecv :: IO ByteString
    }

type WSApp a
    = IO ByteString
   -> (ByteString -> IO ())
   -> (Connection -> IO a)
   -> IO a

websocketsApp :: Request -> Maybe (WSApp a)
websocketsApp req
    -- FIXME handle keep-alive, Upgrade | lookup "connection" reqhs /= Just "Upgrade" = backup sendResponse
    | lookup "upgrade" reqhs /= Just "websocket" = Nothing
    | lookup "sec-websocket-version" reqhs /= Just "13" = Nothing
    | Just key <- lookup "sec-websocket-key" reqhs = Just $ \recvRaw sendRaw app -> do
        let handshake = fromByteString "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: "
                     <> fromByteString (B64.encode key')
                     <> fromByteString "\r\n\r\n"
            key' = SHA1.hash $ key <> "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
        toByteStringIO sendRaw handshake

        src <- mkSource recvRaw

        let recv front0 = waitForFrame src $ \isFinished _opcode _ _ getBS' -> do
                let loop front = do
                        bs <- getBS'
                        if S.null bs
                            then return front
                            else loop $ front . (bs:)
                front <- loop front0
                if isFinished
                    then return $ S.concat $ front []
                    else recv front
        app Connection
            { connSend = \isText payload -> do
                let header = Frame True (if isText then OpText else OpBinary) Nothing $ fromIntegral $ S.length payload
                toByteStringIO sendRaw $ wsDataToBuilder header <> fromByteString payload
            , connRecv = recv id
            }
    | otherwise = Nothing
  where
    reqhs = requestHeaders req

type FrameFinished = Bool
type MaskingKey = Word32
type PayloadSize = Word64

data WSData payload
    = Frame FrameFinished Opcode (Maybe MaskingKey) PayloadSize
    | Payload payload
    deriving Show

data Opcode = OpCont | OpText | OpBinary | OpClose | OpPing | OpPong
    deriving (Show, Eq, Ord, Enum, Bounded)

opcodeToWord8 :: Opcode -> Word8
opcodeToWord8 OpCont = 0x0
opcodeToWord8 OpText = 0x1
opcodeToWord8 OpBinary = 0x2
opcodeToWord8 OpClose = 0x8
opcodeToWord8 OpPing = 0x9
opcodeToWord8 OpPong = 0xA

opcodeFromWord8 :: Word8 -> Maybe Opcode
opcodeFromWord8 =
    flip Map.lookup m
  where
    m = Map.fromList $ map (\o -> (opcodeToWord8 o, o)) [minBound..maxBound]

wsDataToBuilder :: WSData Builder -> Builder
wsDataToBuilder (Payload builder) = builder
wsDataToBuilder (Frame finished opcode mmask payload) =
    fromWord8 byte1
 <> fromWord8 byte2
 <> lenrest
 <> maybe mempty fromWord32be mmask
  where
    byte1 = (if finished then 128 else 0) .|. opcodeToWord8 opcode
    byte2 = (if isJust mmask then 128 else 0) .|. len1

    (len1, lenrest)
        | payload <= 125 = (fromIntegral payload, mempty)
        | payload <= 65536 = (126, fromWord16be $ fromIntegral payload)
        | otherwise = (127, fromWord64be $ fromIntegral payload)

data WSException = ConnectionClosed
                 | RSVBitsSet Word8
                 | InvalidOpcode Word8
    deriving (Show, Typeable)
instance Exception WSException

data Source = Source (IO ByteString) (IORef ByteString)

mkSource :: IO ByteString -> IO Source
mkSource recv = Source recv <$> newIORef S.empty

-- | Guaranteed to never return an empty ByteString.
getBS :: Source -> IO ByteString
getBS (Source next ref) = do
    bs <- readIORef ref
    if S.null bs
        then do
            bs' <- next
            when (S.null bs') (throwIO ConnectionClosed)
            return bs'
        else writeIORef ref S.empty >> return bs

leftover :: Source -> ByteString -> IO ()
leftover (Source _ ref) bs = writeIORef ref bs

getWord8 :: Source -> IO Word8
getWord8 src = do
    bs <- getBS src
    leftover src $ S.tail bs
    return $ S.head bs

getBytes :: (Num word, Bits word) => Source -> Int -> IO word
getBytes src =
    loop 0
  where
    loop total 0 = return total
    loop total remaining = do
        x <- getWord8 src -- FIXME not very efficient, better to use ByteString directly
        loop (shiftL total 8 .|. fromIntegral x) (remaining - 1)

waitForFrame :: Source -> (FrameFinished -> Opcode -> Maybe MaskingKey -> PayloadSize -> IO ByteString -> IO a) -> IO a
waitForFrame src yield = do
    byte1 <- getWord8 src
    byte2 <- getWord8 src

    when (testBit byte1 6 || testBit byte1 5 || testBit byte1 4)
        $ throwIO $ RSVBitsSet byte1

    let opcode' = byte1 .&. 0x0F
    opcode <-
        case opcodeFromWord8 opcode' of
            Nothing -> throwIO $ InvalidOpcode opcode'
            Just o -> return o

    let isFinished = testBit byte1 7
        isMasked = testBit byte2 7
        len' = byte2 `clearBit` 7

    payloadSize <-
        case () of
            ()
                | len' <= 125 -> return $ fromIntegral len'
                | len' == 126 -> getBytes src 2
                | otherwise -> assert (len' == 127) (getBytes src 8)

    mmask <- if isMasked then Just <$> getBytes src 4 else return Nothing
    let unmask' =
            case mmask of
                Nothing -> \_ bs -> bs
                Just mask -> unmask mask

    consumedRef <- newIORef 0
    let getPayload = handlePayload unmask' payloadSize consumedRef

    res <- yield isFinished opcode mmask payloadSize getPayload
    let drain = do
            bs <- getPayload
            unless (S.null bs) drain
    drain
    return res

  where
    handlePayload unmask' totalSize consumedRef = do
        consumed <- readIORef consumedRef
        if consumed >= totalSize
            then return S.empty
            else do
                bs <- getBS src
                let len = fromIntegral $ S.length bs
                    consumed' = consumed + len
                if consumed' <= totalSize
                    then do
                        writeIORef consumedRef consumed'
                        return $ unmask' consumed bs
                    else do
                        let (x, y) = S.splitAt (fromIntegral $ totalSize - consumed) bs
                        leftover src y
                        return $ unmask' consumed x

unmask :: MaskingKey -> Word64 -> ByteString -> ByteString
unmask key offset' masked =
    -- we really want a mapWithIndex...
    fst $ S.unfoldrN len f 0
  where
    len = S.length masked

    f idx | idx >= len = Nothing
    f idx = Just (getIndex idx, idx + 1)

    offset = fromIntegral $ offset' `mod` 4

    getIndex idx = S.index masked idx `xor` maskByte ((offset + idx) `mod` 4)

    maskByte 0 = fromIntegral $ key `shiftR` 24
    maskByte 1 = fromIntegral $ key `shiftR` 16
    maskByte 2 = fromIntegral $ key `shiftR` 8
    maskByte 3 = fromIntegral key
    maskByte i = error $ "Network.Wai.WebSockets.unmask.maskByte: invalid input " ++ show i
