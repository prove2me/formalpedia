-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_positive_gaussian_qscale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:31:58.343383+00:00
-- url     : https://prove2.me/submissions/a4a87183-b135-4387-8435-2583ebc25ce9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_qscale_unchecked_existence
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
  obtain ⟨W, hW⟩ :=
    avram_p4_f6_gaussian_qscale_unchecked_existence X hX q hq hσ
  exact ⟨W, hW, scaleFunction_strict_pos_of_gaussian X q W hW hσ 1 (by norm_num)⟩
