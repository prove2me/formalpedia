-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_clipped_physical_grid_increment_strict_stop_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:16:28.519924+00:00
-- url     : https://prove2.me/submissions/cd001589-98c7-4653-a0ee-58b92d437fe7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} (g : ℕ → ℝ≥0) (hg : Monotone g)
    (ρ : Ω → ℝ≥0) (ω : Ω) (i : ℕ) :
    let u : ℕ → ℝ≥0 := fun j => min (g j) (ρ ω)
    (u (i + 1) - u i =
      if ρ ω ≤ g i then 0 else
        min (g (i + 1)) (ρ ω) - g i) ∧
    (ρ ω ≤ g i → u (i + 1) = u i) := by
  intro u
  constructor
  · by_cases h : ρ ω ≤ g i
    · have hnext : ρ ω ≤ g (i + 1) := h.trans (hg (Nat.le_succ i))
      simp [u, h, min_eq_right h, min_eq_right hnext]
    · have hi : g i ≤ ρ ω :=
        le_of_lt (lt_of_not_ge h)
      simp [u, h, min_eq_left hi]
  · intro h
    have hnext : ρ ω ≤ g (i + 1) := h.trans (hg (Nat.le_succ i))
    simp [u, min_eq_right h, min_eq_right hnext]

