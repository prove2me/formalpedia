-- Prove2me | solution 1 for BitcoinTaproot.checkmultisig_rejected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:39:28.215491+00:00
-- url     : https://prove2.me/submissions/49b1dfe2-b684-46ae-9278-e3a98308ae19

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (c : TapCtx) (ed : ExecData) (fExec : Bool) (ts : TapState) :
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIG ts = none ∧
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIGVERIFY ts = none := by
  constructor <;> simp [tapExecOp, BitcoinScript.OP_IF, BitcoinScript.OP_NOTIF, BitcoinScript.OP_CHECKSIG, BitcoinScript.OP_CHECKSIGVERIFY, OP_CHECKSIGADD, BitcoinScript.OP_CHECKMULTISIG, BitcoinScript.OP_CHECKMULTISIGVERIFY, BitcoinScript.OP_CODESEPARATOR]
