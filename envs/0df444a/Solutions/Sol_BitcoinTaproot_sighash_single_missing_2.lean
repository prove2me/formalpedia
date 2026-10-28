-- Prove2me | solution 2 for BitcoinTaproot.sighash_single_missing
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:13.89592+00:00
-- url     : https://prove2.me/submissions/168206d3-a666-48e3-864c-2575297e7051

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

/-- `SIGHASH_SINGLE` without a corresponding output fails (no `uint256::ONE` quirk in Taproot). -/
theorem solution (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (hv : hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83)) (h3 : hashType &&& 3 = 3) (hout : tx.vout.length ≤ inPos) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by
  unfold sigHashSchnorr
  rw [if_neg (fun hn => hn hv)]
  have hne : hashType ≠ SIGHASH_DEFAULT := by
    unfold SIGHASH_DEFAULT; intro h0; rw [h0] at h3; simp at h3
  dsimp only
  simp only [hne, ite_false, h3, BitcoinSig.SIGHASH_SINGLE, ite_true, hout]
