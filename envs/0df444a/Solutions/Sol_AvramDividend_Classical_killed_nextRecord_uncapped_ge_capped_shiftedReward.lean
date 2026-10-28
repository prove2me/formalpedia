-- Prove2me | solution 1 for AvramDividend.Classical.killed_nextRecord_uncapped_ge_capped_shiftedReward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:15:55.565186+00:00
-- url     : https://prove2.me/submissions/ad2ddefd-4abd-41c0-858d-6d185afc47cd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_countable_twoSided_reward
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) (ω : Ω) :
    (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       let u : ℝ≥0 := (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
       ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
         (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
         let τ : ℕ → ℝ≥0 := fun j =>
           ((Nat.unpair j).2 : ℝ≥0) *
             (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let ρ : ℝ≥0∞ := ⨅ j : ℕ,
           if ε < g (τ j) then (τ j : ℝ≥0∞) else ⊤
         let σ : ℝ≥0∞ := ⨅ j : ℕ,
           if g (τ j) < ε - a then (τ j : ℝ≥0∞) else ⊤
         if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0))
      else 0) ≤
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
     else 0) := by
  by_cases hs : twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
      twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)
  · have hu := firstRecord_capped_clock_eq_uncapped_of_le_horizon X b N ω hs.2
    have hpeak := firstUpcrossing_attains_peak X b hb ω
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal (by
        simpa only [twoSidedExitUpTime] using hu)
    have hBefore :
        (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0∞)) <
          barrierRuinTime X a ω := by
      rw [hu]
      exact hs.1
    have hPoint := killed_nextRecord_weight_ge_countable_twoSided_reward
      X a b ε q ha hb hε ω
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
      hu hpeak.1 hBefore
    simpa only [if_pos hs] using hPoint
  · simp [hs]
