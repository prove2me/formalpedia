-- Prove2me | solution 1 for DetDLP.limb_convolution_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:29.626793+00:00
-- url     : https://prove2.me/submissions/dc4f9eb4-598d-43f2-91df-683782e5715a

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open DetDLP

private lemma bitsToNat_lt_two_pow : ∀ (d : ℕ) (v : Fin d → Bool), bitsToNat v < 2 ^ d
  | 0, v => by
    unfold bitsToNat
    simp
  | d + 1, v => by
    unfold bitsToNat
    rw [Fin.sum_univ_castSucc]
    have hih : (∑ i : Fin d, (if v i.castSucc = true then 1 else 0) * 2 ^ (i.castSucc).val) < 2 ^ d :=
      bitsToNat_lt_two_pow d (fun i => v i.castSucc)
    have hlast : (if v (Fin.last d) = true then 1 else 0) * 2 ^ (Fin.last d).val ≤ 2 ^ d := by
      rw [Fin.val_last]
      by_cases h : v (Fin.last d) = true <;> simp [h]
    rw [pow_succ']
    omega

theorem solution :
    (∀ (d : ℕ) (v : Fin d → Bool), bitsToNat v < 2 ^ d) ∧
    (∀ (d : ℕ), 1 ≤ d →
      0 < d ∧ d ≤ d * 1 ∧ 1 ≤ 2 ^ d ∧
      (fun x : Fin (4 * d) → Bool =>
        let a := bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩)
        let b := bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩)
        let cout := bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)
        let B := 2 ^ d
        let Q := 2 ^ (4 * d) + 1
        let limb (w i : ℕ) := w / B ^ i % B
        let c (u : ℕ) := ∑ i ∈ Finset.range 1, ∑ j ∈ Finset.range 1,
          if i + j = u then limb a i * limb b j else 0
        (∑ u ∈ Finset.range (2 * 1), (c u % Q) * B ^ u) = cout) =
      (fun x : Fin (4 * d) → Bool =>
        bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
        bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
        bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩))) := by
  refine ⟨bitsToNat_lt_two_pow, fun d hd => ⟨by omega, by omega, Nat.one_le_two_pow, ?_⟩⟩
  funext x
  dsimp only
  have ha : bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) < 2 ^ d :=
    bitsToNat_lt_two_pow d _
  have hb : bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) < 2 ^ d :=
    bitsToNat_lt_two_pow d _
  have hab :
      bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
        bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) <
      2 ^ (4 * d) + 1 := by
    have hmul :
        bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
          bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) <
        2 ^ d * 2 ^ d :=
      Nat.mul_lt_mul'' ha hb
    have hpow : 2 ^ d * 2 ^ d ≤ 2 ^ (4 * d) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [show (2 * 1 : ℕ) = 2 by rfl, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Finset.sum_range_one, Nat.add_zero, ↓reduceIte, Nat.reduceEqDiff,
    pow_zero, Nat.div_one, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hab, mul_one, Nat.zero_mod, zero_mul]
