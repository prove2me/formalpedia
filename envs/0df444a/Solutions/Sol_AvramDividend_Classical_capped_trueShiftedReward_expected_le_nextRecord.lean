-- Prove2me | solution 1 for AvramDividend.Classical.capped_trueShiftedReward_expected_le_nextRecord
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:28:45.077+00:00
-- url     : https://prove2.me/submissions/a4e4b93c-b02e-4bbf-aa1e-9e6c73dcebed

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_uncapped_ge_capped_shiftedReward
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

/-- The pathwise capped next-record reward bound survives Lebesgue integration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       let u : ℝ≥0 := (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
       ENNReal.ofReal ε *
         (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
           (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
            let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // ε < g t}, (i.1 : ℝ≥0∞)
            let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < ε - a}, (i.1 : ℝ≥0∞)
            if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
     else 0 ∂P) := by
  apply lintegral_mono
  intro ω
  have hp := killed_nextRecord_uncapped_ge_capped_shiftedReward
    X a b ε q ha hb hε N ω
  by_cases hs : twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
      twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)
  · simp only [if_pos hs] at hp ⊢
    rw [levy_shifted_trueTwoSided_reward_eq_schedule
      X ω ((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
      q ε (ε - a)]
    exact hp
  · simpa only [if_neg hs] using hp
