-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_monotone_stopped_clock_prefix_selector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:33:26.718816+00:00
-- url     : https://prove2.me/submissions/1a694c76-9a82-4a81-a0f7-9b8c988158ea

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

/-- The stopped cells of a finite monotone physical grid form an initial segment. -/
theorem solution
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    ∃ k : Ω → ℕ,
      (∀ ω, k ω ≤ m) ∧
      (∀ ω i, i < m →
        ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω)) := by
  classical
  let hBad (ω : Ω) :
      ∃ j : ℕ, j = m ∨ ¬ ((u j : WithTop ℝ≥0) < τ ω) :=
    ⟨m, Or.inl rfl⟩
  let k : Ω → ℕ := fun ω => Nat.find (hBad ω)
  refine ⟨k, ?_, ?_⟩
  · intro ω
    exact Nat.find_le (h := hBad ω) (Or.inl rfl)
  · intro ω i hi
    constructor
    · intro h
      by_contra hnot
      have hki : k ω ≤ i := Nat.le_of_not_gt hnot
      have hb : k ω = m ∨
          ¬ ((u (k ω) : WithTop ℝ≥0) < τ ω) :=
        Nat.find_spec (hBad ω)
      rcases hb with heq | hNo
      · omega
      · have hle : (u (k ω) : WithTop ℝ≥0) ≤ (u i : WithTop ℝ≥0) :=
          WithTop.coe_le_coe.mpr (hu hki)
        exact hNo (lt_of_le_of_lt hle h)
    · intro hik
      have hNotBad : ¬ (i = m ∨
          ¬ ((u i : WithTop ℝ≥0) < τ ω)) :=
        Nat.find_min (hBad ω) hik
      exact Classical.byContradiction (fun hNo => hNotBad (Or.inr hNo))
