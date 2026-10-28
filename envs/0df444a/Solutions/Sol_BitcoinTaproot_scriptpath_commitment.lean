-- Prove2me | solution 1 for BitcoinTaproot.scriptpath_commitment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:42:01.972798+00:00
-- url     : https://prove2.me/submissions/788c79b4-6dd1-4895-b94d-1b7afdcb30d9

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (spent : List TxOut) (c : BitcoinVerify.Ctx) (stack : List Bytes)
    (script control q : Bytes) (hna : BitcoinTaproot.hasAnnex (stack ++ [script, control]) = false)
    (h : BitcoinTaproot.taprootHandler spent c (stack ++ [script, control]) q = true) :
    BitcoinTaproot.verifyTaprootCommitment control q
      (BitcoinTaproot.tapleafHash (BitVec.ofNat 8 ((control.getD 0 0).toNat &&& BitcoinTaproot.TAPROOT_LEAF_MASK)) script) = true := by
  have e1 : stack ++ [script, control] = (stack ++ [script]) ++ [control] := by simp
  have hlen : (stack ++ [script, control]).length ≠ 1 := by simp
  unfold taprootHandler at h
  simp only [hna, Bool.false_eq_true, if_false] at h
  rw [if_neg (by simp), if_neg hlen, e1, List.getLast?_concat, List.dropLast_concat,
    List.getLast?_concat, List.dropLast_concat] at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i hv
      simpa using hv
