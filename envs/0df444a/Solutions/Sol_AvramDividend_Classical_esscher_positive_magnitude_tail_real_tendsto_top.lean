-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_magnitude_tail_real_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:34:00.800896+00:00
-- url     : https://prove2.me/submissions/2cb1a82c-5a47-4b2e-8eb2-00399ecde834

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_tendsto_top_of_small_band
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_signed_jump_tail_map_identity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Divergence of the reflected Esscher kernel follows from negative-tail divergence. -/
theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfar : ν (Iic (-1 : ℝ)) < ⊤)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (htail : Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun x : ℝ =>
      (((ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | x < (z : ℝ)}).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hweighted : ∀ x : ℝ, 0 < x →
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) < ⊤ := by
    intro x hx
    exact (esscher_weighted_negative_tail_le_unweighted ν φ x hφ hx).trans_lt
      (hfinite x hx)
  have hw := esscher_weighted_negative_tail_real_tendsto_top_of_small_band
    ν φ hφ hfar hfinite hweighted htail
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [(tendsto_atTop.1 hw) M, self_mem_nhdsWithin] with x hx hxpos
  simpa only [esscher_weighted_signed_jump_tail_map_identity ν φ x hxpos] using hx
