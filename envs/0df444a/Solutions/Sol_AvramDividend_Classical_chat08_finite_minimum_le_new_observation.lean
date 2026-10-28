-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_le_new_observation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:02:09.523771+00:00
-- url     : https://prove2.me/submissions/ee6d15f6-563b-454d-87a1-77b0b186c571

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! Including a new observation bounds the first-detection clock by its time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) :
    ∀ (n : ℕ) (ω : Ω),
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
        (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) (n + 1)) ω ≤ τ n ω := by
  intro n ω
  change min (τ n ω)
    ((Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) n) ω) ≤ τ n ω
  exact min_le_left _ _
