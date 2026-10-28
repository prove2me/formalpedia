-- Prove2me | solution 1 for BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T12:25:05.792659+00:00
-- url     : https://prove2.me/submissions/151366ec-fa0e-4ef2-be83-251f9c305510

-- Generated from ChapterSolovayTailDimension.lean — solution of BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
open BookProof.ChapterSolovayTailDimension



noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {m n : ℕ} (h : m ≠ n) :
    substrateInterval m ∩ substrateInterval n = ∅ := by

  wlog hlt : m < n generalizing m n
  · rw [Set.inter_comm]
    exact this (Ne.symm h) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm h))
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hm1, _⟩, ⟨_, hn2⟩⟩
  have hmn : (m : ℝ) + 2 ≤ (n : ℝ) + 1 := by
    have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 2) := by
    apply one_div_le_one_div_of_le hm2 hmn
  linarith
