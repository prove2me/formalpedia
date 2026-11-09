-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail12_original_singular_generator_cell_off_any_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:01:06.779595+00:00
-- url     : https://prove2.me/submissions/d924a43b-f271-4cd1-a828-cd2bff29337a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_actual_reserve_outside_any_band_deficit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A literal original-process singular generator cell lies below any positive
band lower edge with arbitrarily negative discounted sampled contribution. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ y : ℝ, 0 < y ∧ y < a / 2 ∧ y < 1 ∧
      (1 / ((K : ℝ) + 4)) *
        (X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y -
          (1 + y)) ≤ -(K : ℝ) := by
  obtain ⟨y, hy0, hyband, hy1, hs⟩ :=
    avram_bv_tail11_actual_reserve_outside_any_band_deficit K a ha
  have hg :=
    avram_a19_affine_singular_subunit_original_generator_eq X hBV hν y hy0 hy1
  have hp : y ^ (1 / 2 : ℝ) = Real.sqrt y :=
    (Real.sqrt_eq_rpow y).symm
  have hn : y ^ (-(1 / 2 : ℝ)) = (Real.sqrt y)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hy0) (1 / 2 : ℝ)]
    rw [← Real.sqrt_eq_rpow y]
  have hratio : y * (Real.sqrt y)⁻¹ = Real.sqrt y := by
    simpa only [div_eq_mul_inv] using (Real.div_sqrt (x := y))
  refine ⟨y, hy0, hyband, hy1, ?_⟩
  rw [hg, hc, hp, hn]
  have heq :
      0 + (2 * (1 - Real.sqrt y) -
        (1 + y) * (2 * ((Real.sqrt y)⁻¹ - 1))) - (1 + y) =
        3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y := by
    rw [div_eq_mul_inv]
    nlinarith [hratio]
  rw [heq]
  exact hs
