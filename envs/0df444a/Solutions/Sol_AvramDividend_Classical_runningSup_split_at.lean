-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_split_at
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:30:10.582001+00:00
-- url     : https://prove2.me/submissions/6eb24eb2-bf6a-4fff-b7e0-d6e9f673266c

import Mathlib

open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_split_at
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove (f '' Set.Icc 0 (u + t))) :
    sSup (f '' Set.Icc 0 (u + t)) =
      max (sSup (f '' Set.Icc 0 u))
          (sSup (f '' Set.Icc u (u + t))) := by
  have hu : u ≤ u + t := le_add_of_nonneg_right (by positivity)
  have he : Set.Icc 0 (u + t) = Set.Icc 0 u ∪ Set.Icc u (u + t) := by
    ext s
    simp only [Set.mem_Icc, Set.mem_union]
    constructor
    · intro hs
      rcases le_total s u with h | h
      · exact Or.inl ⟨hs.1, h⟩
      · exact Or.inr ⟨h, hs.2⟩
    · rintro (hs | hs)
      · exact ⟨hs.1, hs.2.trans hu⟩
      · exact ⟨(show 0 ≤ u by positivity).trans hs.1, hs.2⟩
  rw [he, Set.image_union] at hb ⊢
  exact csSup_union (hb.mono Set.subset_union_left)
    ((Set.nonempty_Icc.2 (show 0 ≤ u by positivity)).image f)
    (hb.mono Set.subset_union_right) ((Set.nonempty_Icc.2 hu).image f)

theorem solution
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove (f '' Set.Icc 0 (u + t))) :
    sSup (f '' Set.Icc 0 (u + t)) =
      max (sSup (f '' Set.Icc 0 u))
          (sSup (f '' Set.Icc u (u + t))) :=
  AvramDividend.Classical.runningSup_split_at f u t hb

#print axioms solution
