-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux11_original_BV_raw_removed_residual_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:07:07.873114+00:00
-- url     : https://prove2.me/submissions/261cf618-5d25-4fb2-b4d9-328bd6305b42

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_exact_path_of_bounded_laplace_residual_zero
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_integer_laplace_deficit_L1
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_integer_laplace_deficit_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0  := by
  have hpath :=
    AvramDividend.Classical.avram_p3_a_bvdrift_original_exact_path_of_bounded_laplace_residual_zero X hBV
      (AvramDividend.Classical.avram_redux11_original_BV_integer_laplace_deficit_L1 X hX hBV)
      (AvramDividend.Classical.avram_redux11_original_BV_integer_laplace_deficit_mean_zero X hX hBV)
  filter_upwards [hpath] with ω hω
  intro t
  have ht := hω t
  rw [ht]
  ring
