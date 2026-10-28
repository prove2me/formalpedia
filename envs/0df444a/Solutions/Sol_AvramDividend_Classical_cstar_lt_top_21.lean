-- Prove2me | solution 21 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:10:16.475774+00:00
-- url     : https://prove2.me/submissions/d1752672-af40-4f24-b0ff-e1b6339ee8c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_corrected_exit_and_C1
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_bv_standing
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  rcases Classical.em (X.BoundedVariation) with hBV | _
  · exact AvramDividend.Classical.cstar_lt_top_of_bv_standing X hX q hq W hW hBV
  · exact AvramDividend.Classical.cstar_lt_top_of_corrected_exit_and_C1 X hX q hq W hW
      (fun a x ha hx0 hxa =>
        AvramDividend.Classical.two_sided_exit_before_ruin_identity_corrected
          X hX q hq W hW a x ha hx0 hxa)
      (AvramDividend.Classical.scaleFunction_contDiff_one_of_standing X hX q hq W hW)
