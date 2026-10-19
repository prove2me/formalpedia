-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.laplacian_comp_normSq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:52:02.247829+00:00
-- url     : https://prove2.me/submissions/3def7575-3b24-49db-988e-13a9e8dc7341

import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_sum_inner_sq
import Theorems.Thm_BookProof_ChapterRadialLaplacian_diffAt_deriv_of_contDiffAt_two
-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.laplacian_comp_normSq
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem h45_hasFDerivAt_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℝ) • innerCLM E x) x := by
  have h2 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  refine h2.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [show innerCLM E x w = ⟪x, w⟫_ℝ from rfl]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem h45_hasFDerivAt_comp_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : ℝ → ℝ} {y : E} (hd : DifferentiableAt ℝ G (‖y‖ ^ 2)) :
    HasFDerivAt (fun z : E => G (‖z‖ ^ 2)) ((2 * deriv G (‖y‖ ^ 2)) • innerCLM E y) y := by
  have h := hd.hasDerivAt.comp_hasFDerivAt y (h45_hasFDerivAt_normSq y)
  refine h.congr_fderiv ?_
  rw [smul_smul, mul_comm]

theorem h45_fderiv_comp_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    (fderiv ℝ fun z : E => G (‖z‖ ^ 2)) =ᶠ[nhds x]
      fun y => (2 * deriv G (‖y‖ ^ 2)) • (innerCLM E y) := by
  have hc : ContinuousAt (fun y : E => ‖y‖ ^ 2) x := (continuous_norm.pow 2).continuousAt
  have h2 : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 G (‖y‖ ^ 2) :=
    hc.eventually (hG.eventually (by simp))
  filter_upwards [h2] with y hgy
  exact (h45_hasFDerivAt_comp_normSq (hgy.differentiableAt (by norm_num))).fderiv

theorem h45_fderiv_fderiv_comp_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    fderiv ℝ (fderiv ℝ fun y : E => G (‖y‖ ^ 2)) x
      = (2 * deriv G (‖x‖ ^ 2)) • (innerCLM E)
        + ((4 * deriv (deriv G) (‖x‖ ^ 2)) • innerCLM E x).smulRight (innerCLM E x) := by
  have hφ : HasDerivAt (fun r => 2 * deriv G r) (2 * deriv (deriv G) (‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    (BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two hG).hasDerivAt.const_mul 2
  have hc := hφ.comp_hasFDerivAt x (h45_hasFDerivAt_normSq x)
  have hF := hc.smul (innerCLM E).hasFDerivAt
  have h2 : fderiv ℝ (fun y : E => (2 * deriv G (‖y‖ ^ 2)) • innerCLM E y) x = _ := hF.fderiv
  rw [(h45_fderiv_comp_normSq hG).fderiv_eq, h2]
  congr 2
  rw [smul_smul]
  ring_nf

theorem h45_laplacian_comp_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E}
    (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    (Laplacian.laplacian fun y : E => G (‖y‖ ^ 2)) x
      = 4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2)
        + 2 * (Module.finrank ℝ E) * deriv G (‖x‖ ^ 2) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h45_fderiv_fderiv_comp_normSq hG]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  have hterm : ∀ i, 2 * deriv G (‖x‖ ^ 2) * (innerCLM E ((stdOrthonormalBasis ℝ E) i)) ((stdOrthonormalBasis ℝ E) i) +
        4 * deriv (deriv G) (‖x‖ ^ 2) * (innerCLM E x) ((stdOrthonormalBasis ℝ E) i) *
          (innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
      = 2 * deriv G (‖x‖ ^ 2) + 4 * deriv (deriv G) (‖x‖ ^ 2) * ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ ^ 2 := by
    intro i
    rw [show innerCLM E ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)
        = ⟪(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl,
      real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ E).orthonormal.1 i,
      show innerCLM E x ((stdOrthonormalBasis ℝ E) i) = ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl]
    ring
  simp only [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, BookProof.ChapterSolidHarmonicTools.sum_inner_sq x]
  ring

theorem solution [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E}
    (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    (Δ fun y : E => G (‖y‖ ^ 2)) x
      = 4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2)
        + 2 * (Module.finrank ℝ E) * deriv G (‖x‖ ^ 2) := by
  exact h45_laplacian_comp_normSq hG

