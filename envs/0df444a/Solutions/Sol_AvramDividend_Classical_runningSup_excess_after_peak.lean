-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_excess_after_peak
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:30:12.992985+00:00
-- url     : https://prove2.me/submissions/b1f73792-804b-4135-b70d-f896f4b6a50c

import Mathlib

open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_interval_shift
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0) :
    sSup (f '' Set.Icc u (u + t)) =
      sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) := by
  congr 1
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s - u, ⟨by positivity, ?_⟩, ?_⟩
    · exact (tsub_le_iff_right).2 (by simpa [add_comm] using hs.2)
    · dsimp only
      rw [add_tsub_cancel_of_le hs.1]
  · rintro ⟨r, hr, rfl⟩
    exact ⟨u + r, ⟨le_add_of_nonneg_right hr.1, add_le_add_right hr.2 u⟩, rfl⟩


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


theorem AvramDividend.Classical.runningSup_excess_after_peak
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove (f '' Set.Icc 0 (u + t)))
    (hpeak : sSup (f '' Set.Icc 0 u) = f u) :
    sSup (f '' Set.Icc 0 (u + t)) - f u =
      max 0 (sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) - f u) := by
  rw [AvramDividend.Classical.runningSup_split_at f u t hb, hpeak,
    AvramDividend.Classical.runningSup_interval_shift f u t]
  by_cases h : f u ≤ sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t)
  · rw [max_eq_right h, max_eq_right (sub_nonneg.mpr h)]
  · have h' := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (sub_nonpos.mpr h'), sub_self]

theorem solution
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove (f '' Set.Icc 0 (u + t)))
    (hpeak : sSup (f '' Set.Icc 0 u) = f u) :
    sSup (f '' Set.Icc 0 (u + t)) - f u =
      max 0 (sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) - f u) := AvramDividend.Classical.runningSup_excess_after_peak f u t hb hpeak

#print axioms solution

