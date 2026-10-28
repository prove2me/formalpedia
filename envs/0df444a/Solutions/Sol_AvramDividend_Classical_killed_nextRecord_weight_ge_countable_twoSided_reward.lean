-- Prove2me | solution 1 for AvramDividend.Classical.killed_nextRecord_weight_ge_countable_twoSided_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:34:21.715305+00:00
-- url     : https://prove2.me/submissions/c1bd7209-099f-41a1-b6ed-0d4225b5b0f0

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_shifted_twoSided_reward
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Bound the next killed record by its countable, measurable future reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω) :
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
         if ρ < σ then
           ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
         else 0)) ≤
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
     else 0) := by
  classical
  have hdom :=
    killed_nextRecord_weight_ge_shifted_twoSided_reward
      X a b ε q ha hb hε ω u hu hAt hBefore
      (⨅ (r : ℝ≥0)
        (_ : ε < X.X (u + r) ω - X.X u ω), (r : ℝ≥0∞))
      (⨅ (r : ℝ≥0)
        (_ : X.X (u + r) ω - X.X u ω < ε - a),
        (r : ℝ≥0∞))
      rfl rfl
  rw [← levy_shifted_trueTwoSided_reward_eq_schedule
    X ω u q ε (ε - a)]
  simpa only [iInf_subtype] using hdom
