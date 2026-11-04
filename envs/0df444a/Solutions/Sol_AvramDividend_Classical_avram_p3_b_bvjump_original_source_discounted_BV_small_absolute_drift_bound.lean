-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:23:43.933224+00:00
-- url     : https://prove2.me/submissions/4d3ddbbc-b537-45dc-8c9a-8e4d659ed27d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- On the genuine source Lévy measure, nonnegative discounting does not
increase the compact-localised total absolute BV small-jump drift. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (hu : u ∈ Icc (a + 1) b)
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) :
    (∫ z in Ioo (-1 : ℝ) 0,
      |Real.exp (-(q * (t : ℝ))) * (w (u + z) - w u)| ∂X.ν) ≤
      (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) := by
  have ht : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hExp : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq ht))
  have hNonneg : 0 ≤ (∫ z in Ioo (-1 : ℝ) 0,
      |w (u + z) - w u| ∂X.ν) :=
    integral_nonneg (fun z => abs_nonneg _)
  have hEq : (∫ z in Ioo (-1 : ℝ) 0,
        |Real.exp (-(q * (t : ℝ))) * (w (u + z) - w u)| ∂X.ν) =
      Real.exp (-(q * (t : ℝ))) *
        (∫ z in Ioo (-1 : ℝ) 0, |w (u + z) - w u| ∂X.ν) := by
    simp_rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
  rw [hEq]
  calc
    Real.exp (-(q * (t : ℝ))) *
        (∫ z in Ioo (-1 : ℝ) 0, |w (u + z) - w u| ∂X.ν) ≤
      ∫ z in Ioo (-1 : ℝ) 0, |w (u + z) - w u| ∂X.ν := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hExp hNonneg
    _ ≤ (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) :=
      avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
        X hBV w K a b u hLip hu
