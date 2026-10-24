-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_two_positive_of_local_open_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:11:09.209506+00:00
-- url     : https://prove2.me/submissions/539b7876-d9a1-4f05-a668-ae52d917f1ea

import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Local open-interval C2 regularity patches over the positive real half-line. -/
theorem solution
    (W : ℝ → ℝ)
    (hlocal : ∀ x : ℝ, 0 < x →
      ∃ a b : ℝ, a < x ∧ x < b ∧ ContDiffOn ℝ 2 W (Ioo a b)) :
    ContDiffOn ℝ 2 W (Ioi 0) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨a, b, ha, hb, hC2⟩ := hlocal x hx
  refine ⟨Ioo a b, isOpen_Ioo, ⟨ha, hb⟩, ?_⟩
  exact hC2.mono Set.inter_subset_right
