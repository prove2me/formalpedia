-- Prove2me | solution 1 for FatkhullinPolyak.HessStep.hessian_norm_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:11:11.156163+00:00
-- url     : https://prove2.me/submissions/9b89ef47-4c07-4981-ba07-c37db449dfbe

import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

/-- Derivative of `t ↦ f (x + t • v)`. -/
theorem aux_hnub_line_deriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline

/-- Derivative of `t ↦ f' (x + t • v) v` at `0`. -/
theorem aux_hnub_line_deriv2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf' : Differentiable ℝ (fderiv ℝ f)) (x v : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 := (hf' (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  have h2 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero] at h2
  exact h2

/-- Strong convexity gives a lower bound on the Hessian quadratic form. -/
theorem aux_hnub_hess_lower {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hconv : StrongConvexOn Set.univ μ f) (x v : EuclideanSpace ℝ (Fin n)) :
    μ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  set c : ℝ := μ / 2 * ‖v‖ ^ 2 with hc
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - c * t ^ 2
  have hψd : ∀ t, HasDerivAt ψ (fderiv ℝ f (x + t • v) v - c * (2 * t)) t := by
    intro t
    have h := (aux_hnub_line_deriv f hf x v t).fun_sub ((hasDerivAt_pow 2 t).const_mul c)
    simpa [ψ] using h
  have hψconv : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ a b ha hb hab
    have h := hconv.2 (Set.mem_univ (x + s • v)) (Set.mem_univ (x + t • v)) ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hpt : a • (x + s • v) + (1 - a) • (x + t • v) = x + (a * s + (1 - a) * t) • v := by
      module
    have hdiff : (x + s • v) - (x + t • v) = (s - t) • v := by module
    rw [hpt, hdiff, norm_smul, Real.norm_eq_abs] at h
    simp only [mul_pow, sq_abs, smul_eq_mul] at h
    simp only [ψ, smul_eq_mul] at h ⊢
    rw [hc]
    nlinarith [h]
  have hmono : Monotone (deriv ψ) :=
    monotoneOn_univ.mp (hψconv.monotoneOn_deriv fun t _ => (hψd t).differentiableAt)
  have hderiv_eq : deriv ψ = fun t => fderiv ℝ f (x + t • v) v - c * (2 * t) := by
    funext t; exact (hψd t).deriv
  have h2 : HasDerivAt (deriv ψ) (fderiv ℝ (fderiv ℝ f) x v v - c * 2) 0 := by
    rw [hderiv_eq]
    have := (aux_hnub_line_deriv2 f hf' x v).fun_sub (((hasDerivAt_id (0 : ℝ)).const_mul 2).const_mul c)
    simpa using this
  have := h2.nonneg_of_monotone hmono
  rw [hc] at this
  linarith

/-- Descent lemma for functions with Lipschitz gradient. -/
theorem aux_hnub_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x v : EuclideanSpace ℝ (Fin n)) :
    f (x + v) ≤ f x + fderiv ℝ f x v + L / 2 * ‖v‖ ^ 2 := by
  let h : ℝ → ℝ := fun t => f (x + t • v) - t * fderiv ℝ f x v - L / 2 * ‖v‖ ^ 2 * t ^ 2
  have hd : ∀ t, HasDerivAt h
      (fderiv ℝ f (x + t • v) v - fderiv ℝ f x v - L / 2 * ‖v‖ ^ 2 * (2 * t)) t := by
    intro t
    have h1 := ((aux_hnub_line_deriv f hf x v t).fun_sub
      ((hasDerivAt_id t).mul_const (fderiv ℝ f x v))).fun_sub
      ((hasDerivAt_pow 2 t).const_mul (L / 2 * ‖v‖ ^ 2))
    simpa [h] using h1
  have hanti : AntitoneOn h (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := ht
      rw [(hd t).deriv]
      have hg : fderiv ℝ f (x + t • v) v - fderiv ℝ f x v
          = inner ℝ (gradient f (x + t • v) - gradient f x) v := by
        rw [inner_sub_left, inner_gradient_left, inner_gradient_left]
      have hle := real_inner_le_norm (gradient f (x + t • v) - gradient f x) v
      have hLip := hL (x + t • v) x
      have hnorm : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      rw [hnorm] at hLip
      have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
      have : ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ ≤ L * (t * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hLip hv0
      rw [hg]
      nlinarith
  have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  simp only [h, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, mul_one, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  linarith

end FatkhullinPolyak.HessStep

open FatkhullinPolyak.HessStep

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + L / (2 * μ) * hessQuad f x (y - x) := by
  set v := y - x with hv
  have hy : y = x + v := by rw [hv]; abel
  by_cases hv0 : v = 0
  · rw [hv0]
    have : y = x := by rw [hy, hv0, add_zero]
    subst this
    simp [hessQuad]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hL0 : 0 ≤ L := by
    have h := hL y x
    rw [← hv] at h
    have : 0 ≤ L * ‖v‖ := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left this hvpos
  have hA := aux_hnub_descent f L hf hL x v
  have hB := aux_hnub_hess_lower f μ hf hf' hconv x v
  rw [inner_gradient_left, hessQuad]
  rw [← hy] at hA
  have hkey : L / 2 * ‖v‖ ^ 2 ≤ L / (2 * μ) * fderiv ℝ (fderiv ℝ f) x v v := by
    have h1 : 0 ≤ L / (2 * μ) * (fderiv ℝ (fderiv ℝ f) x v v - μ * ‖v‖ ^ 2) :=
      mul_nonneg (div_nonneg hL0 (by positivity)) (by linarith)
    have h2 : L / (2 * μ) * (μ * ‖v‖ ^ 2) = L / 2 * ‖v‖ ^ 2 := by
      field_simp
    nlinarith
  linarith
