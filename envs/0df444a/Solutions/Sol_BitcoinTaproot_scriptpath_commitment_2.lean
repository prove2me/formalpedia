-- Prove2me | solution 2 for BitcoinTaproot.scriptpath_commitment
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:16.845658+00:00
-- url     : https://prove2.me/submissions/0ee26033-54dc-4071-bbd4-a6b52ee88637

import Definitions.Def_BitcoinTaproot

open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

private theorem lexLt_asymm : ∀ (a b : Bytes), lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [lexLt] at h
  | x :: xs, y :: ys, h => by
    simp only [lexLt] at h ⊢
    by_cases h1 : x.toNat < y.toNat
    · rw [if_neg (by omega), if_pos h1]
    · rw [if_neg h1] at h
      by_cases h2 : y.toNat < x.toNat
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [if_neg h2, if_neg h1]
        exact lexLt_asymm xs ys h

private theorem lexLt_total : ∀ (a b : Bytes), lexLt a b = false → lexLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [lexLt] at h
  | _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [lexLt] at h1 h2
    by_cases hxy : x.toNat < y.toNat
    · rw [if_pos hxy] at h1; cases h1
    · rw [if_neg hxy] at h1
      by_cases hyx : y.toNat < x.toNat
      · rw [if_pos hyx] at h2; cases h2
      · rw [if_neg hyx] at h1
        rw [if_neg hyx, if_neg hxy] at h2
        have hx : x = y := by
          have : x.toNat = y.toNat := by omega
          exact BitVec.eq_of_toNat_eq this
        rw [hx, lexLt_total xs ys h1 h2]

/-- A script-path spend that verifies has a valid commitment: the control block's merkle path from the
leaf hash of the revealed script, tweaked into the internal key, is the output key. -/
theorem solution (spent : List TxOut) (c : BitcoinVerify.Ctx) (stack : List Bytes)
    (script control q : Bytes) (hna : BitcoinTaproot.hasAnnex (stack ++ [script, control]) = false)
    (h : BitcoinTaproot.taprootHandler spent c (stack ++ [script, control]) q = true) :
    BitcoinTaproot.verifyTaprootCommitment control q
      (BitcoinTaproot.tapleafHash (BitVec.ofNat 8 ((control.getD 0 0).toNat &&& BitcoinTaproot.TAPROOT_LEAF_MASK)) script) = true := by
  have e : stack ++ [script, control] = (stack ++ [script]) ++ [control] := by simp
  rw [e] at h
  unfold taprootHandler at h
  rw [e] at hna
  simp only [hna, Bool.false_eq_true, ite_false] at h
  have hne : ((stack ++ [script]) ++ [control]).isEmpty = false := by simp
  have hlen : ((stack ++ [script]) ++ [control]).length ≠ 1 := by simp
  simp only [hne, Bool.false_eq_true, ite_false, hlen] at h
  simp only [List.getLast?_concat, List.dropLast_concat] at h
  (try dsimp only at h)
  by_cases hcom : verifyTaprootCommitment control q
      (tapleafHash (BitVec.ofNat 8 ((control.getD 0 0).toNat &&& TAPROOT_LEAF_MASK)) script) = true
  · exact hcom
  · simp only [Bool.not_eq_true] at hcom
    split at h
    · cases h
    · rw [hcom] at h
      simp at h
