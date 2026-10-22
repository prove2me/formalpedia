-- Prove2me | solution 1 for CertDRO.SGD.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:31:19.788368+00:00
-- url     : https://prove2.me/submissions/c00059dc-cd3e-4e1c-b2ed-4faea84527b3

import Mathlib
import Definitions.Def_CertDRO_SGD_model
set_option autoImplicit false
open CertDRO.SGD

theorem gg_descent {d : ℕ} (F : Param d → ℝ) (Lφ : ℝ) (hF : Differentiable ℝ F)
    (hL : ∀ θ θ', ‖gradient F θ - gradient F θ'‖ ≤ Lφ * ‖θ - θ'‖)
    (x h : Param d) :
    F (x + h) ≤ F x + inner ℝ (gradient F x) h + Lφ / 2 * ‖h‖ ^ 2 := by
  set ψ : ℝ → ℝ := fun t => F (x + t • h) - F x - t * inner ℝ (gradient F x) h
      - Lφ * t ^ 2 / 2 * ‖h‖ ^ 2 with hψ
  have hder : ∀ t : ℝ, HasDerivAt ψ
      (inner ℝ (gradient F (x + t • h)) h - inner ℝ (gradient F x) h - Lφ * t * ‖h‖ ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have key : ∀ y : Param d, (fderiv ℝ F y) h = inner ℝ (gradient F y) h := by
      intro y
      simp [gradient, InnerProductSpace.toDual_symm_apply]
    have h2 : HasDerivAt (fun t : ℝ => F (x + t • h)) (inner ℝ (gradient F (x + t • h)) h) t := by
      have := ((hF (x + t • h)).hasFDerivAt).comp_hasDerivAt t h1
      rw [key] at this
      exact this
    have h3 : HasDerivAt (fun t : ℝ => t * inner ℝ (gradient F x) h) (inner ℝ (gradient F x) h) t :=
      ((hasDerivAt_id' t).mul_const (inner ℝ (gradient F x) h)).congr_deriv (one_mul _)
    have h4 : HasDerivAt (fun t : ℝ => Lφ * t ^ 2 / 2 * ‖h‖ ^ 2) (Lφ * t * ‖h‖ ^ 2) t := by
      have := (((hasDerivAt_pow 2 t).const_mul Lφ).div_const 2).mul_const (‖h‖ ^ 2)
      refine this.congr_deriv ?_
      norm_num only [Nat.cast_ofNat, pow_one]
      ring
    exact ((h2.sub (hasDerivAt_const t (F x))).sub h3).sub h4 |>.congr_deriv (by ring)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hder t).continuousAt.continuousWithinAt
    · exact fun t _ => (hder t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t).deriv]
      have hnorm : ‖gradient F (x + t • h) - gradient F x‖ ≤ Lφ * (t * ‖h‖) := by
        have := hL (x + t • h) x
        have e : ‖x + t • h - x‖ = t * ‖h‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
        rwa [e] at this
      have hin : inner ℝ (gradient F (x + t • h) - gradient F x) h ≤ Lφ * (t * ‖h‖) * ‖h‖ :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
      rw [inner_sub_left] at hin
      nlinarith
  have hle := hanti (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) zero_le_one
  have e0 : ψ 0 = 0 := by simp [hψ]
  have e1 : ψ 1 = F (x + h) - F x - inner ℝ (gradient F x) h - Lφ / 2 * ‖h‖ ^ 2 := by
    simp only [hψ, one_smul]; ring
  rw [e0, e1] at hle
  linarith

theorem solution {d : ℕ} (F : Param d → ℝ) (Lφ : ℝ) (hF : Differentiable ℝ F)
    (hL : ∀ θ θ', ‖gradient F θ - gradient F θ'‖ ≤ Lφ * ‖θ - θ'‖)
    (θ g : Param d) (α : ℝ) :
    F (θ - α • g) ≤ F θ - α * (1 - 1 / 2 * Lφ * α) * ‖gradient F θ‖ ^ 2
      + α * (1 - Lφ * α) * inner ℝ (gradient F θ) (gradient F θ - g)
      + Lφ * α ^ 2 / 2 * ‖g - gradient F θ‖ ^ 2 := by
  have h := gg_descent F Lφ hF hL θ (-(α • g))
  rw [← sub_eq_add_neg] at h
  set G := gradient F θ with hG
  have e1 : inner ℝ G (-(α • g)) = -α * inner ℝ G g := by
    rw [inner_neg_right, real_inner_smul_right]; ring
  have e2 : ‖-(α • g)‖ ^ 2 = α ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have e3 : inner ℝ G (G - g) = ‖G‖ ^ 2 - inner ℝ G g := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have e4 : ‖g - G‖ ^ 2 = ‖g‖ ^ 2 - 2 * inner ℝ G g + ‖G‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  rw [e1, e2] at h
  rw [e3, e4]
  nlinarith [h]
