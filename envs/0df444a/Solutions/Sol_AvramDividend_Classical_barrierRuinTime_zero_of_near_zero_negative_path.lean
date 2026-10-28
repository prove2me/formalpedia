-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_negative_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:22:34.058981+00:00
-- url     : https://prove2.me/submissions/8de2a2d4-65a2-44cb-8094-d1e90461aeba

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Negative reserves arbitrarily close to the origin force immediate zero-barrier drawdown ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNeg : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    barrierRuinTime X 0 ω = 0 := by
  apply barrierRuinTime_zero_of_near_zero_drawdown X 0 ω
  intro ε hε
  obtain ⟨t, htε, hXt⟩ := hNeg ε hε
  refine ⟨t, htε, ?_⟩
  change 0 < runningSup X t ω - X.X t ω
  exact sub_pos.mpr
    (lt_of_lt_of_le hXt (runningSup_eq_rawSup_nonneg X t ω).2)