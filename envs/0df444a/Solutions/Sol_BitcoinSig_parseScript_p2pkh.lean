-- Prove2me | solution 1 for BitcoinSig.parseScript_p2pkh
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:34:06.775197+00:00
-- url     : https://prove2.me/submissions/d25bf28a-d63a-4614-884e-f0bd28c36eab

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (h : Bytes) (hh : h.length = 20) :
    BitcoinSig.parseScript (BitcoinSig.p2pkhBytes h) = some (BitcoinScript.p2pkhScript h) := by
  have hl : (p2pkhBytes h).length = 25 := by
    simp [p2pkhBytes, pushBytes, hh, OP_PUSHDATA1]
  have hp : p2pkhBytes h = 0x76 :: 0xa9 :: 20 :: (h ++ [0x88, 0xac]) := by
    simp [p2pkhBytes, pushBytes, hh, OP_PUSHDATA1]
  unfold parseScript
  rw [hl, hp]
  simp [parseScriptAux, getOp, OP_PUSHDATA4, OP_PUSHDATA1, hh, BitcoinScript.p2pkhScript,
    BitcoinScript.OP_DUP, BitcoinScript.OP_HASH160, BitcoinScript.OP_EQUALVERIFY,
    BitcoinScript.OP_CHECKSIG]
