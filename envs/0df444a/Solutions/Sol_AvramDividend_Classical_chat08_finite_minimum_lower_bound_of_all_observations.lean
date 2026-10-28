-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_lower_bound_of_all_observations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:36:16.545694+00:00
-- url     : https://prove2.me/submissions/1eec38f1-8bf2-4be5-aa01-e979345fa52f

import Mathlib.Probability.Process.Stopping

open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} (τ : ℕ → Ω → WithTop ℝ≥0) (t : WithTop ℝ≥0)
    (n : ℕ) (ω : Ω) (hobs : ∀ k, k < n → t ≤ τ k ω) :
    t ≤ (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω := by
  induction n with
  | zero => exact le_top
  | succ m ih =>
    exact le_min (hobs m (Nat.lt_succ_self m)) (ih fun k hk => hobs k (Nat.lt_succ_of_lt hk))
