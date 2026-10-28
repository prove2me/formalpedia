-- Prove2me | solution 20 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:28:36.54056+00:00
-- url     : https://prove2.me/submissions/b26889b8-3c46-4c29-b530-4665c5ede5d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_bv_standing
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_corrected_exit_and_C1
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  by_cases hBV : X.BoundedVariation
  · exact AvramDividend.Classical.cstar_lt_top_of_bv_standing X hX q hq W hW hBV
  · have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x =
          ENNReal.ofReal (W x / W a) := by
      intro a x ha hx hxa
      exact AvramDividend.Classical.unbounded_corrected_exit_scale_identity
        X q hq W hW hBV a x ha hx hxa
    have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
      AvramDividend.Classical.scaleFunction_contDiff_one X hX q hq W hW
    exact AvramDividend.Classical.cstar_lt_top_of_corrected_exit_and_C1
      X hX q hq W hW hExit hreg
