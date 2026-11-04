-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_nonpositive_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:13:49.075964+00:00
-- url     : https://prove2.me/submissions/6deb2628-a19e-4768-a267-3191c8a7a014

import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_nonpositive_null
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The normalised actual original fourth-weighted image is carried by
strictly positive exponential coordinates, including zero extension. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ) :
    (if 0 < h then (ENNReal.ofReal h)⁻¹ •
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
    else (0 : Measure ℝ)) (Iic (0 : ℝ)) = 0 := by
  by_cases hh : 0 < h
  · simp only [if_pos hh, Measure.smul_apply, smul_eq_mul,
      avram_p2_original_fourth_weighted_exp_pushforward_nonpositive_null X
        (Real.toNNReal h), mul_zero]
  · simp [hh]
