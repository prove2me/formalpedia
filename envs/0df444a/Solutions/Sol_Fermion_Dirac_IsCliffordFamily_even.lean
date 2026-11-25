-- Prove2me | solution 1 for Fermion.Dirac.IsCliffordFamily.even
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:29:03.759358+00:00
-- url     : https://prove2.me/submissions/b3b4b097-bffe-4bfb-81e0-c5242dd9f569

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily

open Matrix Complex Fermion.Dirac

theorem solution {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) : Even n := by
  have h00 := hγ (Sum.inl 0) (Sum.inl 0)
  have h11 := hγ (Sum.inr 0) (Sum.inr 0)
  have h01 := hγ (Sum.inl 0) (Sum.inr 0)
  simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] at h00 h11 h01
  set A := γ (Sum.inl 0)
  set B := γ (Sum.inr 0)
  -- `A * A = 1`, `B * B = -1`, `A * B = - (B * A)`
  have hA : A * A = 1 := by
    have : (2 : ℂ) • (A * A) = (2 : ℂ) • 1 := by rw [two_smul]; simpa using h00
    exact smul_right_injective _ two_ne_zero this
  have hB : B * B = -1 := by
    have : (2 : ℂ) • (B * B) = (2 : ℂ) • (-1) := by rw [two_smul]; simpa using h11
    exact smul_right_injective _ two_ne_zero this
  have hAB : A * B = -(B * A) := eq_neg_of_add_eq_zero_left h01
  have hdetA : A.det * A.det = 1 := by rw [← det_mul, hA, det_one]
  have hdetB : B.det * B.det = (-1) ^ n := by
    rw [← det_mul, hB, det_neg, det_one, mul_one, Fintype.card_fin]
  have hBne : B.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdetB
    exact (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)) hdetB.symm
  have hAne : A.det ≠ 0 := by
    intro h; rw [h, mul_zero] at hdetA; exact zero_ne_one hdetA
  have key : A.det * B.det = (-1) ^ n * (B.det * A.det) := by
    rw [← det_mul, hAB, det_neg, det_mul, Fintype.card_fin]
  have hpow : ((-1 : ℂ)) ^ n = 1 := by
    have : (A.det * B.det) * (1 - (-1) ^ n) = 0 := by linear_combination key
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hAne hBne)
    · exact (sub_eq_zero.mp h).symm
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hpow
