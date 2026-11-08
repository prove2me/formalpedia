-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_original_generator_discount_one_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:45:50.747168+00:00
-- url     : https://prove2.me/submissions/5f40ba9c-df41-41c1-9246-ea7fd45a1a75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_original_generator_eq_c
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_global_hjb_piecewise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original Levy generator satisfies the one-discount HJB sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (x : ℝ) (hx : 0 < x) :
    X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x -
      (if x < 0 then (0 : ℝ) else 1 + x) ≤ 0 := by
  have hnonneg : ¬ x < 0 := not_lt.mpr (le_of_lt hx)
  rw [if_neg hnonneg]
  by_cases hx1 : x < 1
  · rw [avram_a19_affine_singular_subunit_original_generator_eq X hBV hν x hx hx1, hc]
    have hp : x ^ (1 / 2 : ℝ) = Real.sqrt x :=
      (Real.sqrt_eq_rpow x).symm
    have hn : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hx) (1 / 2 : ℝ)]
      rw [← Real.sqrt_eq_rpow x]
    have hratio : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
      simpa only [div_eq_mul_inv] using (Real.div_sqrt (x := x))
    have hs : 3 + x - 4 * Real.sqrt x - 2 / Real.sqrt x ≤ 0 := by
      simpa only [if_pos hx1] using
        (avram_a19_affine_singular_global_hjb_piecewise x hx)
    rw [hp, hn]
    rw [div_eq_mul_inv] at hs
    nlinarith [hratio, hs]
  · have hge : 1 ≤ x := le_of_not_gt hx1
    rw [avram_a19_affine_singular_large_reserve_original_generator_eq_c X hBV hν x hge, hc]
    linarith
