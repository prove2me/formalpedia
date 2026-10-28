-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_tendsto_atTop_of_corrected_exit_and_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:00:45.998757+00:00
-- url     : https://prove2.me/submissions/9ef08133-55b8-4026-a862-57bf229b96ec

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Corrected exits and first differentiability make the q-scale derivative coercive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨hpos, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone_of_corrected_exit
      X hX q hq W hW hExit
  exact scale_deriv_tendsto_atTop_of_normalized_monotone
    W φ hφ (hpos 1 zero_lt_one) hmono hdiff
