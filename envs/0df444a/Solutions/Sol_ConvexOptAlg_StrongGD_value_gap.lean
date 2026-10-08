-- Prove2me | solution 1 for ConvexOptAlg.StrongGD.value_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:04:05.41737+00:00
-- url     : https://prove2.me/submissions/bbe21697-1b3a-4288-8a91-f9f5657e1344

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs

set_option autoImplicit false

open scoped InnerProductSpace

open scoped RealInnerProductSpace in
theorem vg350_inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open scoped RealInnerProductSpace in
theorem vg350_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [vg350_inner_grad]
  exact this

open scoped RealInnerProductSpace in
theorem vg350_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := vg350_line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

open scoped RealInnerProductSpace in
theorem vg350_grad_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (v xstar : EuclideanSpace ℝ (Fin n))
    (h : HasGradientAt f v xstar) (hstar : IsMinOn f Set.univ xstar) : v = 0 := by
  have hl : IsLocalMin f xstar := Filter.Eventually.of_forall (fun y => hstar (Set.mem_univ y))
  have hf := (hasGradientAt_iff_hasFDerivAt.mp h)
  have h0 := hl.hasFDerivAt_eq_zero hf
  simpa using h0

open ConvexOptAlg.StrongGD in
theorem solution {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (β : ℝ) (hsm : IsBetaSmooth f g β)
    (xstar : E n) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E n) (η : ℝ) (hrun : IsGDRun g η x) :
    ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xstar ≤ (β / 2) * ‖x t - xstar‖ ^ 2 := by
  intro t _
  obtain ⟨hg, _, hlip⟩ := hsm
  have hgr : ∀ z, gradient f z = g z := fun z => (hg z).gradient
  have hdiff : Differentiable ℝ f := fun z => (hg z).differentiableAt
  have hgrad : ∀ a b, ‖gradient f a - gradient f b‖ ≤ β * ‖a - b‖ := by
    intro a b; rw [hgr, hgr]; exact hlip a b
  have hd := vg350_descent hdiff hgrad xstar (x t)
  have h0 : gradient f xstar = 0 := by
    rw [hgr]; exact vg350_grad_zero f (g xstar) xstar (hg xstar) hstar
  rw [h0, inner_zero_left] at hd
  linarith
