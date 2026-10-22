-- Prove2me | solution 1 for AvramDividend.Classical.chat03_reserve_grid_discount_expectation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:16:51.372912+00:00
-- url     : https://prove2.me/submissions/8940e3be-686b-4564-8d75-49de4d963683

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_exact_uniform_grid_discount_expectation_tendsto
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Specialise the verified discounted grid expectation limit to reserve x
inside upper capital a and lower ruin barrier zero.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a)
    (q : ℝ) (hq : 0 ≤ q) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n => ∫⁻ ω,
        let up := ⨅ k : ℕ,
          if a - x < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        let down := ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < -x then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < down then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
        else 0 ∂P)
      atTop (𝓝 (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
        else 0 ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hsep : -x < a - x := by linarith
  exact chat03_exact_uniform_grid_discount_expectation_tendsto
    X (-x) (a - x) hsep q hq mesh hpos hzero
