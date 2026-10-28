-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_Ioi_of_local_open_intervals
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:23:53.787075+00:00
-- url     : https://prove2.me/submissions/1430e357-3696-495a-a447-dfa9d0e9bbd5

import Mathlib

open Set
theorem solution
    (f : ℝ → ℝ)
    (hlocal : ∀ x : ℝ, 0 < x →
      ∃ a b : ℝ, 0 < a ∧ a < x ∧ x < b ∧ ContDiffOn ℝ 1 f (Ioo a b)) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  obtain ⟨a, b, ha, hax, hxb, hf⟩ := hlocal x hx
  exact ⟨Ioo a b, isOpen_Ioo, ⟨hax, hxb⟩, hf.mono inter_subset_right⟩
