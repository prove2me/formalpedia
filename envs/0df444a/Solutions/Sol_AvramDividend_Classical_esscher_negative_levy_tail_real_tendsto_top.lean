-- Prove2me | solution 1 for AvramDividend.Classical.esscher_negative_levy_tail_real_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:44:47.783636+00:00
-- url     : https://prove2.me/submissions/0b956924-d711-4835-91e3-3b0e5b35158a

import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_tendsto_top_of_small_band
import Mathlib.MeasureTheory.Measure.WithDensity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Infinite Lévy activity persists under any nonnegative Esscher tilt. -/
theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun x : ℝ =>
      ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hfar : ν (Iic (-1 : ℝ)) < ⊤ :=
    negative_jump_truncation_measure_finite ν hνint 1 zero_lt_one
  have hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤ := by
    intro x hx
    have hsub : Iio (-x) ⊆ Iic (-x) := by
      intro y hy
      exact le_of_lt (by simpa only [mem_Iio] using hy)
    exact lt_of_le_of_lt (measure_mono hsub)
      (negative_jump_truncation_measure_finite ν hνint x hx)
  have hweighted : ∀ x : ℝ, 0 < x →
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) < ⊤ := by
    intro x hx
    exact lt_of_le_of_lt
      (esscher_weighted_negative_tail_le_unweighted ν φ x hφ hx)
      (hfinite x hx)
  exact esscher_weighted_negative_tail_real_tendsto_top_of_small_band
    ν φ hφ hfar hfinite hweighted
    (negative_jump_real_tail_tendsto_top ν hνint hνinf)
