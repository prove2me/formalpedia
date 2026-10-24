-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_corrected_exit_scale_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:36:46.966994+00:00
-- url     : https://prove2.me/submissions/5e4dd88a-117a-4d52-a4b6-7e2db96c7cb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectationCorrected X q a x =
      ENNReal.ofReal (W x / W a) := by
  have hWa : 0 < W a :=
    (scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv) a ha
  have hstop_raw :=
    chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  have hstop :
      twoSidedExitExpectationCorrected X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    classical
    unfold twoSidedExitExpectationCorrected
    convert hstop_raw using 1
    congr 2
  rw [ENNReal.ofReal_div_of_pos hWa]
  apply (ENNReal.eq_div_iff
    (ENNReal.ofReal_ne_zero_iff.mpr hWa) (by simp)).2
  simpa [mul_comm] using hstop
