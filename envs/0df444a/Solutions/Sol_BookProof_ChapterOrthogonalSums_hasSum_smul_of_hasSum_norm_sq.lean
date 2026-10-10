-- Prove2me | solution 1 for BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:23.819583+00:00
-- url     : https://prove2.me/submissions/8984f559-b153-4604-bcb8-4e7ec83f1782

-- Generated from ChapterOrthogonalSums.lean — solution of BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq
import Mathlib
import Definitions.Def_ChapterOrthogonalSums
import Theorems.Thm_BookProof_ChapterOrthogonalSums_summable_of_orthogonal_of_summable_norm_sq
import Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_norm_sq_of_hasSum
open BookProof.ChapterOrthogonalSums



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal ℂ v) {y : E}
    (h : HasSum (fun k => ‖⟪v k, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2)) :
    HasSum (fun k => ⟪v k, y⟫_ℂ • v k) y := by

  classical
  set c : ι → ℂ := fun k => ⟪v k, y⟫_ℂ with hc
  have hnormv : ∀ k, ‖v k‖ = 1 := fun k => hv.1 k
  have horth : ∀ i j : ι, i ≠ j → ⟪c i • v i, c j • v j⟫_ℂ = 0 := by
    intro i j hij
    rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i j, if_neg hij]
    simp
  have hnormterm : ∀ k, ‖c k • v k‖ ^ 2 = ‖c k‖ ^ 2 := by
    intro k
    rw [norm_smul, hnormv k, mul_one]
  have hsummable : Summable fun k => c k • v k := by
    refine summable_of_orthogonal_of_summable_norm_sq horth ?_
    simpa only [hnormterm] using h.summable
  obtain ⟨y', hy'⟩ := hsummable
  -- the Fourier coefficients of `y'` are the `c k`
  have hcoeff : ∀ k, ⟪v k, y'⟫_ℂ = c k := by
    intro k
    have h1 : HasSum (fun j => ⟪v k, c j • v j⟫_ℂ) ⟪v k, y'⟫_ℂ := hy'.mapL (innerSL ℂ (v k))
    have h2 : HasSum (fun j => ⟪v k, c j • v j⟫_ℂ) (⟪v k, c k • v k⟫_ℂ) := by
      refine hasSum_single k ?_
      intro j hj
      rw [inner_smul_right, orthonormal_iff_ite.mp hv k j, if_neg (Ne.symm hj)]
      simp
    have h3 : ⟪v k, y'⟫_ℂ = ⟪v k, c k • v k⟫_ℂ := h1.unique h2
    rw [h3, inner_smul_right, orthonormal_iff_ite.mp hv k k, if_pos rfl, mul_one]
  -- `⟪y, y'⟫ = ‖y‖²`
  have hyy' : ⟪y, y'⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : HasSum (fun k => ⟪y, c k • v k⟫_ℂ) ⟪y, y'⟫_ℂ := hy'.mapL (innerSL ℂ y)
    have hterm : ∀ k, ⟪y, c k • v k⟫_ℂ = ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      have h4 : ⟪y, v k⟫_ℂ = (starRingEnd ℂ) (c k) := by rw [hc, inner_conj_symm]
      rw [inner_smul_right, h4, Complex.mul_conj, Complex.sq_norm]
    simp only [hterm] at h1
    have h2 : HasSum (fun k => ((‖c k‖ ^ 2 : ℝ) : ℂ)) ((‖y‖ ^ 2 : ℝ) : ℂ) :=
      h.mapL Complex.ofRealCLM
    exact h1.unique h2
  -- `‖y'‖² = ‖y‖²`
  have hnormy' : ‖y'‖ ^ 2 = ‖y‖ ^ 2 := by
    have h1 := hasSum_norm_sq_of_hasSum hy' horth
    simp only [hnormterm] at h1
    exact h1.unique h
  -- hence `y = y'`
  have hzero : ‖y - y'‖ ^ 2 = 0 := by
    have hre : RCLike.re (((‖y‖ ^ 2 : ℝ) : ℂ)) = ‖y‖ ^ 2 := Complex.ofReal_re _
    rw [norm_sub_sq (𝕜 := ℂ), hyy', hnormy', hre]
    ring
  have : y = y' := by
    have := norm_eq_zero.1 (by nlinarith [norm_nonneg (y - y')] : ‖y - y'‖ = 0)
    exact sub_eq_zero.1 this
  rw [this]
  simp only [hcoeff]
  exact hy'
