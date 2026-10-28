-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scaleDeriv_growth_of_stopped_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:57:24.782185+00:00
-- url     : https://prove2.me/submissions/c345b1c7-667b-40a2-8d6e-d19c519f2a9e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_tilted_scale_mono_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Full derivative growth follows directly from stopped-scale balance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hBalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨hpos, φ, hφ, _hroot, htilt⟩ :=
    chat01_unbounded_tilted_scale_mono_of_stopped_balance
      X q hq W hW hnbv hBalance
  have htilt' : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Ioi 0) := by
    simpa only [neg_mul] using htilt
  exact scale_deriv_tendsto_atTop_of_normalized_monotone
    W φ hφ (hpos 1 (by norm_num)) htilt' hdiff
