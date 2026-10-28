-- Prove2me | solution 2 for AvramDividend.Classical.bv_lower_exit_creeping_reward_eq_inv_drift_mass_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:23:53.653127+00:00
-- url     : https://prove2.me/submissions/1ed20469-07ef-4b81-91bc-146f414c01a8

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_discounted_creeping_factorisation
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
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
      else 0 ∂P) =
      (∫⁻ ω,
        if twoSidedExitDownTime X (-x) ω <
            twoSidedExitUpTime X (a - x) ω ∧
           x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0
        then ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal)))
        else 0 ∂P) * ENNReal.ofReal (1 / X.drift) := by
  rw [chat04_lower_exit_discounted_creeping_factorisation X q W hW a x,
    bv_scale_origin_eq_inv_drift X hX q hq W hW hBV]
