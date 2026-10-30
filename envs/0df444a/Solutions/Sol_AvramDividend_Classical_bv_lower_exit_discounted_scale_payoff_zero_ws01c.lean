-- Prove2me | solution 1 for AvramDividend.Classical.bv_lower_exit_discounted_scale_payoff_zero_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:02:58.347181+00:00
-- url     : https://prove2.me/submissions/72b065c5-77dc-4bf4-b1d6-e4ea1d545b1e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_ae
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_ae_no_creeping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! The genuine BV lower-first exit q-scale reward vanishes because
the stopped reserve cannot contact the boundary exactly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) = 0 := by
  have hNoCreep :
      ∀ᵐ ω ∂P,
        twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω →
        x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by
    simpa only [twoSidedExitDownTime, twoSidedExitUpTime] using
      (bv_strict_lower_exit_no_creeping_ae
        X hX q hq W hW hBV a x ha hx0 hxa)
  exact chat04_lower_exit_lintegral_zero_of_ae_no_creeping
    X q W hW a x hNoCreep
