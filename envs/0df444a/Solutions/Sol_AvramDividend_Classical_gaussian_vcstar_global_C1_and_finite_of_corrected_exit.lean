-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_vcstar_global_C1_and_finite_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:25:31.875141+00:00
-- url     : https://prove2.me/submissions/8717208b-f562-4081-82a7-5bde94f3d4a8

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_cstar_finite_gaussian_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_C1_from_corrected_exit
import Theorems.Thm_AvramDividend_Classical_vcstar_contDiffOn_two_above_real_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    cstar W < ⊤ ∧ ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) := by
  have hc : cstar W < ⊤ :=
    cstar_finite_gaussian_of_corrected_exit_identity
      X hX q hq W hW hσ hExit
  refine ⟨hc, ?_⟩
  by_cases hp : 0 < (cstar W).toReal
  · exact gaussian_vcstar_C1_from_corrected_exit
      X hX q hq W hW hp hσ hExit
  · have hz : (cstar W).toReal = 0 :=
      le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
    have hC2 := vcstar_contDiffOn_two_above_real_cstar W
    have hC2pos : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) := by
      simpa only [hz] using hC2
    exact hC2pos.of_le (by norm_num)
