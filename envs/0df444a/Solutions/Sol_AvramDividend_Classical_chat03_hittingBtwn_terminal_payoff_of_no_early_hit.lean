-- Prove2me | solution 1 for AvramDividend.Classical.chat03_hittingBtwn_terminal_payoff_of_no_early_hit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:07:21.299406+00:00
-- url     : https://prove2.me/submissions/7a18418f-eb28-444c-83d1-92262df17be5

import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-!
A finite bounded hitting-time clock capped beyond T has its stopped
physical time equal to T whenever no index with physical time < T
hits the designated set. Hits at or after T remain permitted, so this
handles the exact terminal-tie case omitted by strict horizon lemmas.
-/
theorem solution
    {Ω β : Type*} (u : ℕ → Ω → β) (s : Set β) (ω : Ω)
    (mesh T : ℝ≥0) (m : ℕ)
    (hcap : T ≤ (m : ℝ≥0) * mesh)
    (hNoEarly : ∀ j : ℕ, (j : ℝ≥0) * mesh < T → u j ω ∉ s) :
    min (((hittingBtwn u s 0 m ω : ℕ) : ℝ≥0) * mesh) T = T := by
  have hKle : hittingBtwn u s 0 m ω ≤ m := hittingBtwn_le ω
  by_cases hKlt : hittingBtwn u s 0 m ω < m
  · have hclock :
        T ≤ ((hittingBtwn u s 0 m ω : ℕ) : ℝ≥0) * mesh := by
      by_contra hn
      have hlt :
          ((hittingBtwn u s 0 m ω : ℕ) : ℝ≥0) * mesh < T :=
        lt_of_not_ge hn
      have hmem : u (hittingBtwn u s 0 m ω) ω ∈ s :=
        hittingBtwn_mem_set_of_hittingBtwn_lt hKlt
      exact (hNoEarly _ hlt) hmem
    exact min_eq_right hclock
  · have hKeq : hittingBtwn u s 0 m ω = m :=
      Nat.le_antisymm hKle (Nat.le_of_not_gt hKlt)
    rw [hKeq]
    exact min_eq_right hcap
