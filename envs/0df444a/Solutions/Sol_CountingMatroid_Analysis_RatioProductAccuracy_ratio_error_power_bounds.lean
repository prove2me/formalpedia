-- Prove2me | solution 1 for CountingMatroid.Analysis.RatioProductAccuracy.ratio_error_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:44:30.158336+00:00
-- url     : https://prove2.me/submissions/9eb6eca6-44bb-4f77-aaf7-75f0ffb1214d

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
set_option autoImplicit false

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RatioProductAccuracy

/-- INTERNAL: Bernoulli's inequality bounds the accumulated relative-error
factors for the paper's choice of η, without passing through real logarithms.
TEXLINE: main.tex:1290-1311 -/
theorem solution (L : ℕ) (ε : ℚ)
    (hε : 0 < ε) (hεone : ε < 1) :
    let η := ε / (32 * ((L : ℚ) + 1))
    1 - ε / 4 ≤ ((1 - η) / (1 + η)) ^ L ∧
      ((1 + η) / (1 - η)) ^ L ≤ 1 + ε / 4 := by
  let η := ε / (32 * ((L : ℚ) + 1))
  have hL : (0 : ℚ) ≤ L := Nat.cast_nonneg L
  have hden : (0 : ℚ) < 32 * ((L : ℚ) + 1) := by positivity
  have hη : 0 < η := div_pos hε hden
  have hηsmall : η < 1 / 32 := by
    dsimp [η]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hbudget : 2 * (L : ℚ) * η ≤ ε / 16 := by
    have heq : η * (32 * ((L : ℚ) + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  let a := (1 - η) / (1 + η)
  let b := (1 + η) / (1 - η)
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hb : 0 < b := div_pos (by linarith) (by linarith)
  have halower : 1 - 2 * η ≤ a := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + η)).mpr
    nlinarith [sq_nonneg η]
  have hbern := one_add_mul_sub_le_pow (by linarith : -1 ≤ a) L
  have hapow : 1 - ε / 16 ≤ a ^ L := by
    have hmul := mul_le_mul_of_nonneg_left halower hL
    nlinarith
  have hab : a * b = 1 := by
    dsimp [a, b]
    field_simp [ne_of_gt (show 0 < 1 - η by linarith),
      ne_of_gt (show 0 < 1 + η by linarith)]
  have habpow : a ^ L * b ^ L = 1 := by rw [← mul_pow, hab, one_pow]
  change 1 - ε / 4 ≤ a ^ L ∧ b ^ L ≤ 1 + ε / 4
  constructor
  · linarith
  · have hmul := mul_le_mul_of_nonneg_right hapow (pow_nonneg hb.le L)
    have hproduct : 1 ≤ (1 - ε / 16) * (1 + ε / 4) := by
      nlinarith [mul_pos hε (sub_pos.mpr hεone)]
    nlinarith
