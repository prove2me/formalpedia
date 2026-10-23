-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_damped_square_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:41:41.707144+00:00
-- url     : https://prove2.me/submissions/091c1229-d511-4982-a6ec-cb3816829e95

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    Real.exp (-(φ * z)) * z ^ 2 ≤
      (1 + 2 / φ) * (Real.exp (-(φ * z / 2)) * min (z ^ 2) z) := by
  have hnonneg : 0 ≤ φ * z / 2 := by positivity
  have hepos : 0 < Real.exp (-(φ * z / 2)) := Real.exp_pos _
  have hele : Real.exp (-(φ * z / 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  have hcoeff : 1 ≤ 1 + 2 / φ := by
    have : 0 ≤ 2 / φ := by positivity
    linarith
  have hbase :
      Real.exp (-(φ * z / 2)) * z ^ 2 ≤
        (1 + 2 / φ) * min (z ^ 2) z := by
    by_cases hz1 : z ≤ 1
    · have hsq : z ^ 2 ≤ z := by nlinarith
      rw [min_eq_left hsq]
      calc
        _ ≤ 1 * z ^ 2 :=
          mul_le_mul_of_nonneg_right hele (sq_nonneg z)
        _ ≤ (1 + 2 / φ) * z ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg z)
    · have hzone : 1 ≤ z := le_of_lt (lt_of_not_ge hz1)
      have hsq : z ≤ z ^ 2 := by nlinarith
      rw [min_eq_right hsq]
      have hexp : φ * z / 2 ≤ Real.exp (φ * z / 2) := by
        have hh := Real.add_one_le_exp (φ * z / 2)
        linarith
      have hprod : Real.exp (-(φ * z / 2)) * (φ * z / 2) ≤ 1 := by
        calc
          _ ≤ Real.exp (-(φ * z / 2)) * Real.exp (φ * z / 2) :=
            mul_le_mul_of_nonneg_left hexp hepos.le
          _ = 1 := by rw [← Real.exp_add]; simp
      have hscaled : Real.exp (-(φ * z / 2)) * z ≤ 2 / φ := by
        apply (le_div_iff₀ hφ).2
        nlinarith [hprod]
      have hc : Real.exp (-(φ * z / 2)) * z ≤ 1 + 2 / φ := by
        linarith
      calc
        Real.exp (-(φ * z / 2)) * z ^ 2 =
            (Real.exp (-(φ * z / 2)) * z) * z := by ring
        _ ≤ (1 + 2 / φ) * z :=
          mul_le_mul_of_nonneg_right hc hz
  have hexp :
      Real.exp (-(φ * z)) =
        Real.exp (-(φ * z / 2)) * Real.exp (-(φ * z / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  calc
    _ = Real.exp (-(φ * z / 2)) *
        (Real.exp (-(φ * z / 2)) * z ^ 2) := by ring
    _ ≤ Real.exp (-(φ * z / 2)) *
        ((1 + 2 / φ) * min (z ^ 2) z) :=
      mul_le_mul_of_nonneg_left hbase hepos.le
    _ = (1 + 2 / φ) *
        (Real.exp (-(φ * z / 2)) * min (z ^ 2) z) := by ring
