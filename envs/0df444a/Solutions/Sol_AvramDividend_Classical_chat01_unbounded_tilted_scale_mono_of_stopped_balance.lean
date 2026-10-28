-- Prove2me | solution 1 for AvramDividend.Classical.chat01_unbounded_tilted_scale_mono_of_stopped_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:52:54.145019+00:00
-- url     : https://prove2.me/submissions/9b8aa076-9fc5-412a-a1ff-7354ff04c37e

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Once the stopped-scale identity is available, positivity, positive-root
    existence and monotonicity of the tilted scale follow together. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hBalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
        MonotoneOn (fun x : ℝ => Real.exp (-(φ * x)) * W x)
          (Ioi (0 : ℝ)) := by
  apply unbounded_positive_tilt_of_corrected_exit X q hq W hW hnbv
  intro a x ha hx0 hxa
  exact chat01_unbounded_corrected_exit_ratio_of_stopped_balance
    X q hq W hW hnbv a x ha hx0 hxa
    (hBalance a x ha hx0 hxa)
