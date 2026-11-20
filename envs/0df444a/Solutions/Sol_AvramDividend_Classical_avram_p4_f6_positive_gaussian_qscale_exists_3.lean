-- Prove2me | solution 3 for AvramDividend.Classical.avram_p4_f6_positive_gaussian_qscale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:16:01.232194+00:00
-- url     : https://prove2.me/submissions/0e7efed5-ab69-4d64-a649-a39afcbdcc28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_true_positive_discount_qscale_exists
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W ∧ 0 < W 1  := by
  have hBV : ¬ X.BoundedVariation := by
    intro hvar
    have hzero : X.σ = 0 := hvar.1
    linarith
  obtain ⟨W, hW⟩ :=
    avram_f6_original_UBV_true_positive_discount_qscale_exists
      X hX hBV q hq
  exact ⟨W, hW,
    scaleFunction_strict_pos_of_gaussian X q W hW hσ 1 (by norm_num)⟩
