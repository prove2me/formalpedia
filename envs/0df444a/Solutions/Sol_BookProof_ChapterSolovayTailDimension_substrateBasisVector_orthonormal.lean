-- Prove2me | solution 1 for BookProof.ChapterSolovayTailDimension.substrateBasisVector_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T12:25:07.812686+00:00
-- url     : https://prove2.me/submissions/e2f5d68f-5556-43c9-bd4c-ec7bd64626ba

-- Generated from ChapterSolovayTailDimension.lean — solution of BookProof.ChapterSolovayTailDimension.substrateBasisVector_orthonormal
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
import Theorems.Thm_BookProof_ChapterSolovayTailDimension_substrateIntervals_disjoint
import Theorems.Thm_BookProof_ChapterSolovayTailDimension_norm_substrateBasisVector
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovayTailDimension



noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution : Orthonormal ℝ substrateBasisVector := by

  rw [orthonormal_iff_ite]
  intro m n
  by_cases h : m = n
  · subst h
    rw [real_inner_self_eq_norm_sq, norm_substrateBasisVector]
    norm_num
  · simp only [if_neg h]
    rw [substrateBasisVector, substrateBasisVector,
      L2.inner_indicatorConstLp_indicatorConstLp, substrateIntervals_disjoint h,
      measureReal_empty, zero_smul]
