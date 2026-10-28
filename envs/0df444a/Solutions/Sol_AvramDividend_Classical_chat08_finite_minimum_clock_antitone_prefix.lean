-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_clock_antitone_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:59:24.841019+00:00
-- url     : https://prove2.me/submissions/e43bad24-25f8-450b-af81-3952736df234

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! A finite minimum clock decreases when an additional observation is included. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) :
    ∀ (n : ℕ) (ω : Ω),
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) (n + 1)) ω ≤
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) n) ω := by
  intro n ω
  change min (τ n ω)
    ((Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) n) ω) ≤
    ((Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) n) ω)
  exact min_le_right _ _
