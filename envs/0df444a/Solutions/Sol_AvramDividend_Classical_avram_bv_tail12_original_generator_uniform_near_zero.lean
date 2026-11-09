-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail12_original_generator_uniform_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:18:38.062101+00:00
-- url     : https://prove2.me/submissions/c41c5af9-6b53-438a-b805-b015c982c701

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All sufficiently small literal reserves force a large negative original
Levy generator contribution over the exact reciprocal physical grid width. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (K : ℕ) (y : ℝ) (hy : 0 < y)
    (hy1 : y < 1)
    (hy_small : y ≤ (1 / ((K : ℝ) + 4)) ^ 4) :
    (1 / ((K : ℝ) + 4)) *
      (X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y -
        (1 + y)) ≤ -(K : ℝ) := by
  have hroot :
      Real.sqrt ((1 / ((K : ℝ) + 4)) ^ 4) =
        (1 / ((K : ℝ) + 4)) ^ 2 := by
    rw [show (1 / ((K : ℝ) + 4)) ^ 4 =
      ((1 / ((K : ℝ) + 4)) ^ 2) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hbound :
      Real.sqrt y ≤ (1 / ((K : ℝ) + 4)) ^ 2 := by
    calc
      Real.sqrt y ≤ Real.sqrt ((1 / ((K : ℝ) + 4)) ^ 4) :=
        Real.sqrt_le_sqrt hy_small
      _ = _ := hroot
  have hs := avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
    K (Real.sqrt y) (Real.sqrt_pos.2 hy) hbound
  have hy_sq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy.le
  rw [hy_sq] at hs
  have hg :=
    avram_a19_affine_singular_subunit_original_generator_eq X hBV hν y hy hy1
  have hp : y ^ (1 / 2 : ℝ) = Real.sqrt y :=
    (Real.sqrt_eq_rpow y).symm
  have hn : y ^ (-(1 / 2 : ℝ)) = (Real.sqrt y)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hy) (1 / 2 : ℝ)]
    rw [← Real.sqrt_eq_rpow y]
  have hratio : y * (Real.sqrt y)⁻¹ = Real.sqrt y := by
    simpa only [div_eq_mul_inv] using (Real.div_sqrt (x := y))
  rw [hg, hc, hp, hn]
  have heq :
      0 + (2 * (1 - Real.sqrt y) -
        (1 + y) * (2 * ((Real.sqrt y)⁻¹ - 1))) - (1 + y) =
        3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y := by
    rw [div_eq_mul_inv]
    nlinarith [hratio]
  rw [heq]
  exact hs
