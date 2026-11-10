-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys17_original_postright_reserve_source_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:34:54.683171+00:00
-- url     : https://prove2.me/submissions/93327477-86f2-489b-afd4-46291607606f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0),
      (x + X.X t ω - rightLimit D t ω) -
        (x + X.X s ω - rightLimit D s ω) =
      ((t : ℝ) - (s : ℝ)) * X.drift -
        ((∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) -
         (∑' v : ℝ≥0, if 0 < v ∧ v ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        (rightLimit D t ω - rightLimit D s ω) := by
  filter_upwards [
    avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  ] with ω hraw
  intro s t
  have hs := hraw s
  have ht := hraw t
  linear_combination hs - ht
