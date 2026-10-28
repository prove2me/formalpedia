-- Prove2me | solution 1 for AvramDividend.Classical.bv_zero_residual_prefix_before_reflected_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:22:36.55884+00:00
-- url     : https://prove2.me/submissions/1410cdad-08d9-4c8b-8190-857d27adc511

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_prefix_runningSup_linear
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A full zero-residual prefix survives the original strict zero-drawdown ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (ω : Ω) (t : ℝ≥0)
    (hHistory : ∀ s : ℝ≥0, s ≤ t →
      (s : ℝ) * X.drift - X.X s ω = 0) :
    (t : ℝ≥0∞) ≤ barrierRuinTime X 0 ω := by
  unfold barrierRuinTime
  refine le_iInf fun s => le_iInf fun hs => ?_
  by_contra hle
  have hst : s < t := by
    exact_mod_cast (lt_of_not_ge hle)
  have hXs := hHistory s hst.le
  have hSs :=
    bv_actual_residual_zero_prefix_runningSup_linear
      X hStanding hBV ω t hHistory s hst.le
  have hdraw : drawdown X s ω = 0 := by
    dsimp [drawdown, reflectedSup]
    rw [hSs]
    linarith
  rw [hdraw] at hs
  exact (lt_irrefl (0 : ℝ)) hs
