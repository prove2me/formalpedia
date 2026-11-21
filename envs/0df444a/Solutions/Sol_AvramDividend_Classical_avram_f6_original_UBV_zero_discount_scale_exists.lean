-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_zero_discount_scale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T18:54:41.607182+00:00
-- url     : https://prove2.me/submissions/61bf0d9d-2ace-4ad9-8bef-339c9311d74a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_discount_scale_exists
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_UBV_zero_discount_scale_exists
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) :
    ∃ W₀ : ℝ → ℝ, IsScaleFunction X 0 W₀ := by
  by_cases hσ : X.σ = 0
  · exact avram_f6_purejump_UBV_zero_discount_scale_exists X hX hBV hσ
  · rcases lt_or_eq_of_le X.σ_nonneg with hpos | heq
    · exact avram_p4_f6_gaussian_zero_discount_scale_exists X hX hpos
    · exact False.elim (hσ heq.symm)
