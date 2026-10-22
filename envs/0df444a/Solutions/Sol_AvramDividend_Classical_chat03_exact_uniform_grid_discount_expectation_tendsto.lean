-- Prove2me | solution 1 for AvramDividend.Classical.chat03_exact_uniform_grid_discount_expectation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:08:34.716726+00:00
-- url     : https://prove2.me/submissions/95483d4a-f0a6-499e-9c70-36fea1efb869

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_exact_uniform_grid_upperfirst_payoff_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Under the exact sampled clocks, the upper-first discounted expectation
converges to the continuous two-sided strict-exit expectation.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (hq : 0 ≤ q) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n => ∫⁻ ω,
        let up := ⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        let down := ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < down then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
        else 0 ∂P)
      atTop (𝓝 (∫⁻ ω,
        if twoSidedExitUpTime X upper ω <
            twoSidedExitDownTime X lower ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0 ∂P)) := by
  apply chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
    P q hq
    (fun n ω => ⨅ k : ℕ,
      if upper < X.X ((k : ℝ≥0) * mesh n) ω then
        (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞)
    (fun n ω => ⨅ k : ℕ,
      if X.X ((k : ℝ≥0) * mesh n) ω < lower then
        (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞)
    (fun ω => twoSidedExitUpTime X upper ω)
    (fun ω => twoSidedExitDownTime X lower ω)
  · intro n
    exact (chat03_uniform_grid_passage_clocks_measurable
      X lower upper (mesh n)).1
  · intro n
    exact (chat03_uniform_grid_passage_clocks_measurable
      X lower upper (mesh n)).2
  · exact Filter.Eventually.of_forall fun ω =>
      chat03_exact_uniform_grid_upperfirst_payoff_tendsto
        X ω lower upper hsep q mesh hpos hzero
