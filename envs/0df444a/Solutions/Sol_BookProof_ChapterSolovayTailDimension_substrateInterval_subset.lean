-- Prove2me | solution 1 for BookProof.ChapterSolovayTailDimension.substrateInterval_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T12:25:02.397783+00:00
-- url     : https://prove2.me/submissions/d9d2b660-f17e-47e4-8818-1213d77382da

-- Generated from ChapterSolovayTailDimension.lean — solution of BookProof.ChapterSolovayTailDimension.substrateInterval_subset
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
open BookProof.ChapterSolovayTailDimension



noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : substrateInterval n ⊆ Icc (0 : ℝ) 1 := by

  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  constructor
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  · have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1]; linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
