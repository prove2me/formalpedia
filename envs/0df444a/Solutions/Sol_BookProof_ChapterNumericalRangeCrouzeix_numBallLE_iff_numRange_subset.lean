-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:55.058707+00:00
-- url     : https://prove2.me/submissions/1ccf100e-e5e4-44f5-bee3-fda2a43fd8e0

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numRadiusLE_iff_numRange_subset
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_inner_sub_const_smul
import Theorems.Thm_BookProof_ChapterH9_mem_numRange
import Definitions.Def_ChapterH9
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] (A : E →L[ℂ] E) (c : ℂ) {r : ℝ} :
    NumBallLE A c r ↔ BookProof.ChapterH9.numRange A ⊆ Metric.closedBall c r := by

  rw [NumBallLE, numRadiusLE_iff_numRange_subset]
  constructor
  · rintro h w ⟨x, hx, rfl⟩
    have hmem : (⟪ x, (A - c • (1 : E →L[ℂ] E)) x ⟫_ℂ)
        ∈ BookProof.ChapterH9.numRange (A - c • (1 : E →L[ℂ] E)) :=
      BookProof.ChapterH9.mem_numRange x hx
    have hb := h hmem
    rw [Metric.mem_closedBall, Complex.dist_eq, inner_sub_const_smul A c x, hx] at hb
    rw [Metric.mem_closedBall, Complex.dist_eq]
    simp only [ContinuousLinearMap.coe_coe]
    simpa using hb
  · rintro h w ⟨x, hx, rfl⟩
    have hb := h (BookProof.ChapterH9.mem_numRange (X := A) x hx)
    rw [Metric.mem_closedBall, Complex.dist_eq] at hb
    rw [Metric.mem_closedBall, Complex.dist_eq]
    simp only [ContinuousLinearMap.coe_coe]
    rw [inner_sub_const_smul A c x, hx]
    simpa using hb
