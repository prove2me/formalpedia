-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:24:42.639857+00:00
-- url     : https://prove2.me/submissions/e31b301d-ef90-40b5-9e9d-76027f5ea1ef

import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_hasFDerivAt_rclmPow
import Theorems.Thm_BookProof_ChapterLaplacianProduct_sum_inner_mul_apply
import Theorems.Thm_BookProof_ChapterLaplacianProduct_laplacian_mul
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_normSqPow
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_rclmPow
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_sum
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_sum_inner_sq
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_rclmPow
-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm
open BookProof.ChapterRadialLaplacian
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

theorem h44_laplacian_normSqPow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (m : ℕ) (x : E) :
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

theorem h44_laplacian_cylTerm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (e : E) (he : ‖e‖ = 1) (j m : ℕ) (x : E) :
    (Δ fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x
      = (j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m)
            * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1) := by
  have hL : (fun y : E => (⟪e, y⟫_ℝ) ^ j) = fun y => (innerCLM E e y) ^ j := rfl
  have hc1 : ContDiffAt ℝ 2 (fun y : E => (⟪e, y⟫_ℝ) ^ j) x :=
    (BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow (innerCLM E e) j).contDiffAt
  rw [BookProof.ChapterLaplacianProduct.laplacian_mul hc1
      (BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow m).contDiffAt,
    h44_laplacian_normSqPow, h44_fderiv_normSqPow, hL,
    BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow,
    (BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow (innerCLM E e) j x).fderiv]
  have h1 : ∑ i, (innerCLM E e ((stdOrthonormalBasis ℝ E) i)) ^ 2 = 1 := by
    have h := BookProof.ChapterSolidHarmonicTools.sum_inner_sq e
    rw [he, one_pow] at h
    rw [← h]; rfl
  have h2 : ∑ i, (((j : ℝ) * (innerCLM E e x) ^ (j - 1)) • innerCLM E e) ((stdOrthonormalBasis ℝ E) i)
      * ((2 * (m : ℝ) * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
      = (j : ℝ) * (innerCLM E e x) ^ (j - 1) * (2 * (m : ℝ) * (‖x‖ ^ 2) ^ (m - 1)) * innerCLM E e x := by
    rw [← BookProof.ChapterLaplacianProduct.sum_inner_mul_apply (innerCLM E e) x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show innerCLM E x ((stdOrthonormalBasis ℝ E) i) = ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl]
    ring
  rw [h1, h2]
  rw [show innerCLM E e x = ⟪e, x⟫_ℝ from rfl]
  rcases j with _ | j
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

theorem solution (e : E) (he : ‖e‖ = 1) (j m : ℕ) (x : E) :
    (Δ fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x
      = (j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m)
            * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1) := by
  exact h44_laplacian_cylTerm e he j m x

