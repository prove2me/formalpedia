-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_pointwise_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:33:47.385739+00:00
-- url     : https://prove2.me/submissions/3b8da3cc-02c8-4670-994a-3995ed81ab35

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-! The finite first-passage clock is monotone in its observed times. -/
theorem solution
    {Ω : Type*} (τ υ : ℕ → Ω → WithTop ℝ≥0)
    (hτυ : ∀ k ω, τ k ω ≤ υ k ω) :
    ∀ n ω, (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω ≤
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (υ j ω) (σ ω)) n) ω := by
  intro n
  induction n with
  | zero =>
      intro ω
      exact le_refl _
  | succ n ih =>
      intro ω
      change min (τ n ω) ((Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
        (fun _ : Ω => ⊤) (fun j σ ω => min (τ j ω) (σ ω)) n) ω) ≤
        min (υ n ω) ((Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
        (fun _ : Ω => ⊤) (fun j σ ω => min (υ j ω) (σ ω)) n) ω)
      exact min_le_min (hτυ n ω) (ih ω)
