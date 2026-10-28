-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_stopping_times_nat_rec
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:38:42.697984+00:00
-- url     : https://prove2.me/submissions/c9d114f6-b9a6-4776-8d9d-c3399fa2a185

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! Finite minima of arbitrary stopping clocks remain stopping times without filtration continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ)
    (τ : ℕ → Ω → WithTop ℝ≥0)
    (hτ : ∀ k, IsStoppingTime ℱ (τ k)) :
    ∀ n : ℕ, IsStoppingTime ℱ
      (Nat.rec (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) n) := by
  intro n
  induction n with
  | zero =>
      intro r
      simpa using
        (MeasurableSet.empty : MeasurableSet[ℱ r] (∅ : Set Ω))
  | succ n ih =>
      exact (hτ n).min ih
