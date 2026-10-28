-- Prove2me | solution 1 for BitcoinTaproot.sigops_budget
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:39:41.360104+00:00
-- url     : https://prove2.me/submissions/c2a754a3-1e34-42e0-bf62-2a52d6281a48

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey sig : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: sig :: rest) (hsig : sig ≠ []) (hw : ts.weightLeft < BitcoinTaproot.VALIDATION_WEIGHT_PER_SIGOP_PASSED) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts = none := by
  have : ts.weightLeft - VALIDATION_WEIGHT_PER_SIGOP_PASSED < 0 := by omega
  simp [tapExecOp, hs, evalChecksigTapscript, hsig, this, BitcoinScript.OP_IF, BitcoinScript.OP_NOTIF, BitcoinScript.OP_CHECKSIG, BitcoinScript.OP_CHECKSIGVERIFY, OP_CHECKSIGADD, BitcoinScript.OP_CHECKMULTISIG, BitcoinScript.OP_CHECKMULTISIGVERIFY, BitcoinScript.OP_CODESEPARATOR]
