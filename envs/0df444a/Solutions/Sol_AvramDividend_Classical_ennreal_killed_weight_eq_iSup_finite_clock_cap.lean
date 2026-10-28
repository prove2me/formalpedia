-- Prove2me | solution 1 for AvramDividend.Classical.ennreal_killed_weight_eq_iSup_finite_clock_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:57:29.138722+00:00
-- url     : https://prove2.me/submissions/858fc5c8-d0e6-41a7-b7b7-fc46e20c850b

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Basic

open scoped ENNReal
theorem solution
    {Ω : Type*} (T : Ω → ℝ≥0∞) (weight : Ω → ℝ≥0∞)
    (hzero : ∀ ω, T ω = ⊤ → weight ω = 0) (ω : Ω) :
    (⨆ n : ℕ, if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) = weight ω := by 
  by_cases h : T ω = ⊤
  · rw [hzero ω h]; simp
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
    apply le_antisymm
    · exact iSup_le fun m => by split_ifs <;> simp
    · exact le_iSup_of_le n (by rw [if_pos hn.le])
