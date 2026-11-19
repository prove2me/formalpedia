-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f6_positive_gaussian_qscale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:15:48.733203+00:00
-- url     : https://prove2.me/submissions/c9b2c8c2-3244-4b91-8576-32f2d9628a8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_discount_scale_exists
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W ∧ 0 < W 1 := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hv
    exact (ne_of_gt hσ) hv.1
  obtain ⟨W₀, hW₀⟩ := avram_p4_f6_gaussian_zero_discount_scale_exists X hX hσ
  obtain ⟨Wq, hWq⟩ :=
    unbounded_positive_discount_scale_exists_from_zero X hnbv W₀ hW₀ q hq
  exact ⟨Wq, hWq,
    scaleFunction_strict_pos_of_gaussian X q Wq hWq hσ 1 (by norm_num)⟩
