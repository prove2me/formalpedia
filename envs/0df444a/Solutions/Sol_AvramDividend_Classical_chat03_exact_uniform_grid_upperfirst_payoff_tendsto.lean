-- Prove2me | solution 1 for AvramDividend.Classical.chat03_exact_uniform_grid_upperfirst_payoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:00:21.77121+00:00
-- url     : https://prove2.me/submissions/acba3dd5-1e50-4b95-84bd-09eb1f3be323

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_lower_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_grid_discount_tendsto_from_clock_convergence
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The exact upper-first sampled discounted payoff converges pathwise
to the official strict two-sided exit reward for vanishing positive grids.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n =>
        let up := ⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        let down := ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < down then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
        else 0)
      atTop
      (𝓝 (if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0)) := by
  apply chat03_official_grid_discount_tendsto_from_clock_convergence
    X ω lower upper hsep q
    (fun n => ⨅ k : ℕ,
      if upper < X.X ((k : ℝ≥0) * mesh n) ω then
        (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞)
    (fun n => ⨅ k : ℕ,
      if X.X ((k : ℝ≥0) * mesh n) ω < lower then
        (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞)
  · exact chat03_official_upper_grid_clock_tendsto
      X ω upper mesh hpos hzero
  · exact chat03_official_lower_grid_clock_tendsto
      X ω lower mesh hpos hzero
  · intro hInf n
    exact chat03_official_no_upper_exit_grid_inf_top
      X ω upper (mesh n) hInf
