-- Prove2me | solution 1 for AvramDividend.Classical.lower_survival_closed_horizon_pathwise_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:25:17.013972+00:00
-- url     : https://prove2.me/submissions/3630161a-1983-4cbf-98bc-84e4b6965799

import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

open Set
open scoped NNReal
theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (s u : ℝ≥0) (hsu : s ≤ u) :
    {ω : Ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + Y v ω} =
      {ω : Ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + Y v ω} ∩
      {ω : Ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + Y s ω) + (Y v ω - Y s ω)} := by 
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, add_sub_cancel]
  constructor
  · intro h
    exact ⟨fun v hv => h v (hv.trans hsu), fun v _ hv => by
      have := h v hv; linarith⟩
  · rintro ⟨h1, h2⟩ v hv
    rcases le_total v s with hvs | hvs
    · exact h1 v hvs
    · have := h2 v hvs hv; linarith
