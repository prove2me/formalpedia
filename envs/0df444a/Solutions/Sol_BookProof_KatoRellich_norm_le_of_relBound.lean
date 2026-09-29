-- Prove2me | solution 1 for BookProof.KatoRellich.norm_le_of_relBound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T03:21:58.742723+00:00
-- url     : https://prove2.me/submissions/a503d87a-7ed7-41ed-adb0-94c19a60597e

-- Generated from ChapterKatoRellichRelative.lean — solution of BookProof.KatoRellich.norm_le_of_relBound
import Mathlib
import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterEsaClosureCore

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- Swapping the arguments of the inner product flips the sign of the imaginary part. -/
private theorem sol_inner_im_swap (a b : F) :
    (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

/-- The expectation value of an operator symmetric on `D` is real. -/
private theorem sol_inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [sol_inner_im_swap (T x) (x : F)] at h
  linarith

/-- Pythagoras for a symmetric operator: `H x` and `d i x` are orthogonal because
`⟪H x, x⟫` is real. -/
private theorem sol_norm_sub_smul_sq (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  have h1 : (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (H x) (x : F) := inner_smul_right _ _ _
  have h2 : RCLike.re (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ) = 0 := by
    rw [h1]; simp [sol_inner_apply_self_im H hH x]
  have h3 : ‖((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = d ^ 2 * ‖(x : F)‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  rw [h2, h3]; ring

set_option maxHeartbeats 1000000 in
theorem solution (H B : D →ₗ[ℂ] F) (hH : SymmetricOn D H) {a b e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : e ≠ 0)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) (x : D) :
    ‖B x‖ ≤ (a + b / |e|) * ‖H x - ((e : ℂ) * Complex.I) • (x : F)‖ := by
  have he0 : (0 : ℝ) < |e| := abs_pos.mpr he
  set N : ℝ := ‖H x - ((e : ℂ) * Complex.I) • (x : F)‖ with hN
  have hsq : N ^ 2 = ‖H x‖ ^ 2 + e ^ 2 * ‖(x : F)‖ ^ 2 := sol_norm_sub_smul_sq H hH e x
  have hN0 : 0 ≤ N := norm_nonneg _
  have h1 : ‖H x‖ ≤ N := by
    nlinarith [norm_nonneg (H x), sq_nonneg (e * ‖(x : F)‖), norm_nonneg (x : F),
      sq_nonneg ‖(x : F)‖]
  have h2 : |e| * ‖(x : F)‖ ≤ N := by
    nlinarith [norm_nonneg (H x), norm_nonneg (x : F), sq_abs e,
      mul_nonneg (abs_nonneg e) (norm_nonneg (x : F))]
  have h3 : b * ‖(x : F)‖ ≤ (b / |e|) * N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ he0]
    nlinarith
  calc ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖ := hrel x
    _ ≤ a * N + (b / |e|) * N := by nlinarith
    _ = (a + b / |e|) * N := by ring
