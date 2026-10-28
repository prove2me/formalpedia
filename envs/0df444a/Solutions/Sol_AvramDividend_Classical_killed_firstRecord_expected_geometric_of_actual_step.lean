-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_expected_geometric_of_actual_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:26:48.143965+00:00
-- url     : https://prove2.me/submissions/8c6c209a-bfb7-420f-bc63-0ebb34f01af7

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_lower_of_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
/-! Geometric lower estimates for the actual killed first-record weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) (hp : 0 ≤ p)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0)
    (hbase : ENNReal.ofReal (ε * p) ≤ (∫⁻ ω, w 0 ω ∂P))
    (hstep : ∀ n, ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) ≤
      (∫⁻ ω, w (n + 1) ω ∂P)) :
    ∀ n, ENNReal.ofReal (ε * p ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P) := by
  have hw' : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (ε + (n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (ε + (n : ℝ) * ε) ω).toReal)))
      else 0 := by
    intro n ω
    have hindex : (((n + 1 : ℕ) : ℝ) * ε) = ε + (n : ℝ) * ε := by
      push_cast
      ring
    rw [hw n ω, hindex]
  exact killed_firstRecord_grid_geometric_expected_lower_of_step
    X a ε q ε p hq hε hp w hw' hbase hstep
