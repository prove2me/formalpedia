-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_clock_eq_top_of_all_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:07:51.306998+00:00
-- url     : https://prove2.me/submissions/7b4492d8-2ecf-42e3-b6de-b299bc1a3995

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! No finite-prefix detection means the first-detection clock remains infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) :
    ∀ (n : ℕ) (ω : Ω),
      (∀ k : ℕ, k < n → τ k ω = ⊤) →
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) n) ω = ⊤ := by
  intro n
  induction n with
  | zero =>
      intro ω h
      rfl
  | succ n ih =>
      intro ω h
      change min (τ n ω)
        ((Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
          (fun _ : Ω => (⊤ : WithTop ℝ≥0))
          (fun k σ ω => min (τ k ω) (σ ω)) n) ω) = ⊤
      have hprior : ∀ k : ℕ, k < n → τ k ω = ⊤ := by
        intro k hk
        exact h k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [h n (Nat.lt_succ_self n), ih ω hprior]
      simp
