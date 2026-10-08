-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_interval_shift
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:29:47.629225+00:00
-- url     : https://prove2.me/submissions/76db9b8e-9537-425f-bf10-982953fe866f

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

theorem solution
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0) :
    sSup (f '' Set.Icc u (u + t)) =
      sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) :=
  AvramDividend.Classical.runningSup_interval_shift f u t

#print axioms solution
