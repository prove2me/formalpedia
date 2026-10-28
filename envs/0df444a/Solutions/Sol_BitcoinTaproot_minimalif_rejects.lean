-- Prove2me | solution 1 for BitcoinTaproot.minimalif_rejects
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:39:32.765214+00:00
-- url     : https://prove2.me/submissions/6c5f85f0-d5bf-4362-8871-bdccc3a4e80c

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (c : TapCtx) (ed : ExecData) (ts : TapState) (top : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = top :: rest) (h : 1 < top.length ∨ (top.length = 1 ∧ (top.getD 0 0).toNat ≠ 1)) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_IF ts = none := by
  simp only [List.getD_eq_getElem?_getD] at h
  simp [tapExecOp, hs, h, BitcoinScript.OP_IF, BitcoinScript.OP_NOTIF, BitcoinScript.OP_CHECKSIG, BitcoinScript.OP_CHECKSIGVERIFY, OP_CHECKSIGADD, BitcoinScript.OP_CHECKMULTISIG, BitcoinScript.OP_CHECKMULTISIGVERIFY, BitcoinScript.OP_CODESEPARATOR]
  intro h1 h2
  rcases h with h | ⟨h3, h4⟩
  · omega
  · exact absurd (h2 h3) h4
