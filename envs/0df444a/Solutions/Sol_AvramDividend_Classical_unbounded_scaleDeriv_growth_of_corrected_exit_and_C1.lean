-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scaleDeriv_growth_of_corrected_exit_and_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:11:16.681081+00:00
-- url     : https://prove2.me/submissions/df279c52-5a99-4180-a474-69d11031036d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Corrected first passage and smoothness force scale-derivative growth. -/
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
  obtain ⟨hpos, φ, hφ, _, htilt⟩ :=
    unbounded_positive_tilt_of_corrected_exit X q hq W hW hnbv hExit
  have htilt' : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using htilt
  exact scale_deriv_tendsto_atTop_of_normalized_monotone
    W φ hφ (hpos 1 zero_lt_one) htilt' hdiff
