-- Prove2me | solution 4 for AvramDividend.Classical.avram_p4_f6_positive_gaussian_qscale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:19:33.981039+00:00
-- url     : https://prove2.me/submissions/53a69983-918a-4696-ac82-b22091c30f86
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
    ∃ W : ℝ → ℝ, IsScaleFunction X q W ∧ 0 < W 1 := by
  have hBV : ¬ X.BoundedVariation := by
    intro hBV
    have hσzero : X.σ = 0 := hBV.1
    have : (0 : ℝ) < 0 := by simpa [hσzero] using hσ
    exact (lt_irrefl (0 : ℝ)) this
  obtain ⟨W, hW⟩ :=
    avram_f6_original_UBV_true_positive_discount_qscale_exists
      X hX hBV q hq
  exact ⟨W, hW,
    scaleFunction_strict_pos_of_gaussian X q W hW hσ 1 (by norm_num)⟩
