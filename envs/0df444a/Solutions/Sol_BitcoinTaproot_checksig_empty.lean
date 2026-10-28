-- Prove2me | solution 1 for BitcoinTaproot.checksig_empty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:39:36.552681+00:00
-- url     : https://prove2.me/submissions/22b29519-c5b7-4553-b667-97d50575a122

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: [] :: rest) (hpk : pubkey.length = 32) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts =
      some { ts with st := { ts.st with stack := BitcoinScript.boolBytes false :: rest } } := by
  simp [tapExecOp, hs, evalChecksigTapscript, hpk, BitcoinScript.OP_IF, BitcoinScript.OP_NOTIF, BitcoinScript.OP_CHECKSIG, BitcoinScript.OP_CHECKSIGVERIFY, OP_CHECKSIGADD, BitcoinScript.OP_CHECKMULTISIG, BitcoinScript.OP_CHECKMULTISIGVERIFY, BitcoinScript.OP_CODESEPARATOR]
