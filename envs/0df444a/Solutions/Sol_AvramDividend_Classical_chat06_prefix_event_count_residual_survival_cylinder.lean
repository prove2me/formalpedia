-- Prove2me | solution 1 for AvramDividend.Classical.chat06_prefix_event_count_residual_survival_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:53:39.213266+00:00
-- url     : https://prove2.me/submissions/d1d96ffb-b0eb-49f6-8cff-067853c1bb7c

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A fixed-count event intersected with an observed-prefix event
and survival for a nonnegative additional time is an arrival cylinder. -/
theorem solution
    {Ω E : Type*} (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock) (n : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (Z : Ω → E) (Q : Set E) :
    {ω : Ω | Z ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)} =
      {ω : Ω | Z ω ∈ Q ∧
        (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} := by
  ext ω
  have hCyl :=
    AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
      (fun i => τ i ω) (N ω) (hThreshold ω) clock hclock n
  have hSucc :
      (∑ i ∈ Finset.range (n + 1), τ i ω) =
        (∑ i ∈ Finset.range n, τ i ω) + τ n ω :=
    Finset.sum_range_succ (fun i => τ i ω) n
  change
    (Z ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)) ↔
      (Z ω ∈ Q ∧ (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω)
  rw [hCyl, hSucc]
  constructor
  · rintro ⟨hq, ⟨hl, _⟩, hsurv⟩
    exact ⟨hq, hl, by linarith⟩
  · rintro ⟨hq, hl, hsurv⟩
    exact ⟨hq, ⟨hl, by linarith⟩, by linarith⟩
