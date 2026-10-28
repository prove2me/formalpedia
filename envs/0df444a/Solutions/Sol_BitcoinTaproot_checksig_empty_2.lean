-- Prove2me | solution 2 for BitcoinTaproot.checksig_empty
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:12.511652+00:00
-- url     : https://prove2.me/submissions/8d61d537-fb8a-4883-8b31-369f6c9c1d5d

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

/-- An empty signature is a clean `false` (no weight consumed, no key check) for a 32-byte key. -/
theorem solution (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: [] :: rest) (hpk : pubkey.length = 32) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts =
      some { ts with st := { ts.st with stack := BitcoinScript.boolBytes false :: rest } } := by
  unfold tapExecOp
  rw [if_neg (by decide)]
  simp only [BEq.rfl, Bool.true_or, ite_true, hs]
  unfold evalChecksigTapscript
  simp [hpk, show ¬ (BitcoinScript.OP_CHECKSIG = BitcoinScript.OP_CHECKSIGVERIFY) by decide]
