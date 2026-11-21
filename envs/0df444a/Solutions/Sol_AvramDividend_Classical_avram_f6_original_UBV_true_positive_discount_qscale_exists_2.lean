-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_UBV_true_positive_discount_qscale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:12:57.082451+00:00
-- url     : https://prove2.me/submissions/38f3a0fb-a3b2-45ab-b5b4-2d36bdcd290b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_zero_discount_scale_exists
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W := by
  classical
  obtain ⟨W₀, hW₀⟩ :=
    avram_f6_original_UBV_zero_discount_scale_exists X hX hBV
  exact unbounded_positive_discount_scale_exists_from_zero
    X hBV W₀ hW₀ q hq
