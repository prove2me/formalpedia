-- Prove2me | solution 2 for BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:23:27.304498+00:00
-- url     : https://prove2.me/submissions/04959d4d-571b-48df-b928-5054e82d713c

import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Theorems.Thm_BookProof_ChapterLaplacianProduct_laplacian_mul
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_normSqPow
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_rclmPow
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_sum
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_sum_inner_sq
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_rclmPow
-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem h44_fderiv_normSqPow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) (x : E) :
    fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x = (2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x := by
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  refine (h2.pow m).fderiv.trans ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [show innerCLM E x w = ⟪x, w⟫_ℝ from rfl]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem h44_fderiv_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    fderiv ℝ (fun y : E => ‖y‖ ^ 2) x = (2 : ℝ) • innerCLM E x := by
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  refine h2.fderiv.trans ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [show innerCLM E x w = ⟪x, w⟫_ℝ from rfl]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem h44_laplacian_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (x : E) : (Δ fun y : E => ‖y‖ ^ 2) x = 2 * (Module.finrank ℝ E : ℝ) := by
  have hf : (fun y : E => ‖y‖ ^ 2) = fun y => ∑ i, (innerCLM E ((stdOrthonormalBasis ℝ E) i) y) ^ 2 := by
    funext y
    rw [← BookProof.ChapterSolidHarmonicTools.sum_inner_sq y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show innerCLM E ((stdOrthonormalBasis ℝ E) i) y = ⟪(stdOrthonormalBasis ℝ E) i, y⟫_ℝ from rfl,
      real_inner_comm]
  rw [hf, BookProof.ChapterSolidHarmonicTools.laplacian_sum]
  · have : ∀ i, (Δ fun y => (innerCLM E ((stdOrthonormalBasis ℝ E) i) y) ^ 2) x = 2 := by
      intro i
      rw [BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow]
      have h := BookProof.ChapterSolidHarmonicTools.sum_inner_sq ((stdOrthonormalBasis ℝ E) i)
      rw [(stdOrthonormalBasis ℝ E).orthonormal.1 i] at h
      have h' : ∑ j, (innerCLM E ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)) ^ 2 = 1 := by
        rw [one_pow] at h; rw [← h]; rfl
      rw [h']
      norm_num
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro i _
    exact (BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow _ 2).contDiffAt

theorem solution (m : ℕ) (x : E) :
    (Δ fun y : E => (‖y‖ ^ 2) ^ m) x
      = (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m) * (‖x‖ ^ 2) ^ (m - 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hfun : (fun y : E => (‖y‖ ^ 2) ^ (k + 1)) = fun y => (‖y‖ ^ 2) ^ k * ‖y‖ ^ 2 := by
      funext y; ring
    rw [hfun, BookProof.ChapterLaplacianProduct.laplacian_mul
      (BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow k).contDiffAt (contDiff_norm_sq ℝ).contDiffAt,
      ih, h44_laplacian_normSq, h44_fderiv_normSqPow, h44_fderiv_normSq]
    have hs : ∑ i, ((2 * (k : ℝ) * (‖x‖ ^ 2) ^ (k - 1)) • innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
        * ((2 : ℝ) • innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
        = 4 * k * (‖x‖ ^ 2) ^ (k - 1) * ‖x‖ ^ 2 := by
      rw [← BookProof.ChapterSolidHarmonicTools.sum_inner_sq x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show innerCLM E x ((stdOrthonormalBasis ℝ E) i) = ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl]
      ring
    rw [hs]
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

