-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_scaleDeriv_growth_of_corrected_exit_and_C1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:12:47.017996+00:00
-- url     : https://prove2.me/submissions/f84913d7-c8e1-4101-aff8-d3114a1aaf95

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨hpos, φ, hφ, -, hmono⟩ :=
    AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit X q hq W hW hnbv hExit
  refine AvramDividend.Classical.scale_deriv_tendsto_atTop_of_normalized_monotone W φ hφ
    (hpos 1 one_pos) ?_ hdiff
  simpa only [neg_mul] using hmono
