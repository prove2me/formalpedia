-- Prove2me | solution 1 for CertDRO.SGD.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:31:49.221001+00:00
-- url     : https://prove2.me/submissions/c75eec88-15da-46eb-b1f0-fb87e89e7748

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
    (hL : ∀ θ θ', ‖gradient F θ - gradient F θ'‖ ≤ Lφ * ‖θ - θ'‖) (hLφ : 0 ≤ Lφ)
    (θ g u : Param d) (α : ℝ) (hα : 0 ≤ α) (hαL : Lφ * α ≤ 1) :
    F (θ - α • g) ≤ F θ - α / 2 * ‖gradient F θ‖ ^ 2
      + α * (1 - Lφ * α) * inner ℝ (gradient F θ) (gradient F θ - u)
      + α * (1 + Lφ * α) / 2 * ‖g - u‖ ^ 2
      + Lφ * α ^ 2 * ‖u - gradient F θ‖ ^ 2 := by
  have h := gg_descent F Lφ hF hL θ (-(α • g))
  rw [← sub_eq_add_neg] at h
  set G := gradient F θ with hG
  obtain ⟨δ, e, rfl, rfl⟩ : ∃ δ e : Param d, g = G + δ + e ∧ u = G + e :=
    ⟨g - u, u - G, by abel, by abel⟩
  have e1 : ‖G + δ‖ ^ 2 = ‖G‖ ^ 2 + 2 * inner ℝ G δ + ‖δ‖ ^ 2 := norm_add_sq_real _ _
  have e2 : ‖G + δ + e‖ ^ 2 = ‖G + δ‖ ^ 2 + 2 * (inner ℝ G e + inner ℝ δ e) + ‖e‖ ^ 2 := by
    rw [norm_add_sq_real, inner_add_left]
  have e3 : ‖δ - e‖ ^ 2 = ‖δ‖ ^ 2 - 2 * inner ℝ δ e + ‖e‖ ^ 2 := norm_sub_sq_real _ _
  have e4 : inner ℝ G (G + δ + e) = ‖G‖ ^ 2 + inner ℝ G δ + inner ℝ G e := by
    rw [inner_add_right, inner_add_right, real_inner_self_eq_norm_sq]
  have e5 : inner ℝ G (G - (G + e)) = - inner ℝ G e := by
    rw [show G - (G + e) = -e by abel, inner_neg_right]
  have e6 : ‖G + δ + e - (G + e)‖ = ‖δ‖ := by congr 1; abel
  have e7 : ‖G + e - G‖ = ‖e‖ := by congr 1; abel
  have e8 : ‖-(α • (G + δ + e))‖ ^ 2 = α ^ 2 * ‖G + δ + e‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have e9 : inner ℝ G (-(α • (G + δ + e))) = -α * inner ℝ G (G + δ + e) := by
    rw [inner_neg_right, real_inner_smul_right]; ring
  rw [e8, e9] at h
  rw [e5, e6, e7]
  have p1 : 0 ≤ α * (1 - Lφ * α) / 2 * ‖G + δ‖ ^ 2 :=
    mul_nonneg (by have : 0 ≤ 1 - Lφ * α := by linarith
                   positivity) (sq_nonneg _)
  have p2 : 0 ≤ Lφ * α ^ 2 / 2 * ‖δ - e‖ ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  rw [e4] at h
  rw [e2, e1] at h
  rw [e1] at p1
  rw [e3] at p2
  nlinarith [h, p1, p2]
