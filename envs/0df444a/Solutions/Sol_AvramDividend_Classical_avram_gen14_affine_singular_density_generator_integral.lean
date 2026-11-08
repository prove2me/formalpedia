-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen14_affine_singular_density_generator_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:49:12.173356+00:00
-- url     : https://prove2.me/submissions/94973420-ff41-42c5-8a02-ba99dfbfc0dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen14_affine_small_negative_band_piecewise
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_density_restrict_integral
import Theorems.Thm_AvramDividend_Classical_avram_gen13_affine_crossing_negative_jump_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Integrating the original crossing-only generator against the singular negative Levy density. -/
theorem solution (x : ℝ) (hx : 0 < x) (hcap : x < 1) :
    (∫ z, SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z
      ∂(volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) =
      2 * (1 - x ^ (1 / 2 : ℝ)) -
        (1 + x) * (2 * (x ^ (-(1 / 2 : ℝ)) - 1)) := by
  rw [avram_gen14_singular_density_restrict_integral]
  have hset : Ioo (-1 : ℝ) 0 ∩ Iio (-x) = Ioo (-1 : ℝ) (-x) := by
    ext z
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨hl, _⟩, ht⟩
      exact ⟨hl, ht⟩
    · rintro ⟨hl, ht⟩
      exact ⟨⟨hl, lt_trans ht (neg_lt_zero.mpr hx)⟩, ht⟩
  calc
    (∫ z in Ioo (-1 : ℝ) 0,
      |z| ^ (-(3 / 2 : ℝ)) *
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z ∂volume) =
      (∫ z in Ioo (-1 : ℝ) 0,
        |z| ^ (-(3 / 2 : ℝ)) *
          (if z < -x then -1 - x - z else 0) ∂volume) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro z hz
        exact congrArg (fun v : ℝ => |z| ^ (-(3 / 2 : ℝ)) * v)
          (avram_gen14_affine_small_negative_band_piecewise x z hx hcap hz)
    _ = (∫ z in Ioo (-1 : ℝ) 0,
          (Iio (-x)).indicator
            (fun z => |z| ^ (-(3 / 2 : ℝ)) * (-1 - x - z)) z ∂volume) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro z hz
        by_cases h : z < -x
        · rw [Set.indicator_of_mem (show z ∈ Iio (-x) from h)]
          simp [h]
        · rw [Set.indicator_of_notMem (show z ∉ Iio (-x) from h)]
          simp [h]
    _ = (∫ z in Ioo (-1 : ℝ) 0 ∩ Iio (-x),
          |z| ^ (-(3 / 2 : ℝ)) * (-1 - x - z) ∂volume) := by
        rw [setIntegral_indicator measurableSet_Iio]
    _ = (∫ z in Ioo (-1 : ℝ) (-x),
          |z| ^ (-(3 / 2 : ℝ)) * (-1 - x - z) ∂volume) := by
        rw [hset]
    _ = (∫ z in (-1 : ℝ)..(-x),
          (-1 - x - z) * |z| ^ (-(3 / 2 : ℝ))) := by
        rw [intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ -x)]
        rw [integral_Ioc_eq_integral_Ioo]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro z hz
        ring
    _ = 2 * (1 - x ^ (1 / 2 : ℝ)) -
        (1 + x) * (2 * (x ^ (-(1 / 2 : ℝ)) - 1)) := by
        exact avram_gen13_affine_crossing_negative_jump_integral x hx (le_of_lt hcap)
