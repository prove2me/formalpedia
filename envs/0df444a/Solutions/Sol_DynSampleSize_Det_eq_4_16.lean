-- Prove2me | solution 1 for DynSampleSize.Det.eq_4_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:10:32.691576+00:00
-- url     : https://prove2.me/submissions/937586e6-a663-4dd5-8efb-0786f0e4223b

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting
set_option autoImplicit false
open Filter Topology
open DynSampleSize.Det

theorem solution {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (g w : ℕ → EuclideanSpace ℝ (Fin m))
    (hw : ∀ k, w (k + 1) = w k - ((1 - θ) / L) • g k) (k : ℕ)
    (h48 : ‖g k - gradient J (w k)‖ ≤ θ * ‖g k‖) :
    J (w (k + 1)) ≤ J (w k) - beta θ / L * ‖gradient J (w k)‖ ^ 2 := by
  obtain ⟨hC, hlam, hlamL, hess⟩ := hJ
  have hL : 0 < L := lt_trans hlam hlamL
  have descent : ∀ x s : EuclideanSpace ℝ (Fin m),
      J (x + s) ≤ J x + fderiv ℝ J x s + L / 2 * ‖s‖ ^ 2 := by
    intro x s
    have hJd : Differentiable ℝ J := hC.differentiable (by norm_num)
    have hf1 : Differentiable ℝ (fderiv ℝ J) :=
      (hC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    set c : ℝ := L * ‖s‖ ^ 2 with hc
    let γ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => x + t • s
    have hγ : ∀ t, HasDerivAt γ s t := fun t => by
      exact (((hasDerivAt_id t).smul_const s).const_add x).congr_deriv (one_smul ℝ s)
    have hφ : ∀ t, HasDerivAt (fun t => J (γ t)) (fderiv ℝ J (γ t) s) t := fun t =>
      (hJd (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    have hφ' : ∀ t, HasDerivAt (fun t => fderiv ℝ J (γ t) s)
        (fderiv ℝ (fderiv ℝ J) (γ t) s s) t := by
      intro t
      have h1 : HasDerivAt (fun t => fderiv ℝ J (γ t)) (fderiv ℝ (fderiv ℝ J) (γ t) s) t :=
        (hf1 (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
      simpa using h1.clm_apply (hasDerivAt_const t s)
    let ψ : ℝ → ℝ := fun t => J x + fderiv ℝ J x s * t + c * t ^ 2 / 2 - J (γ t)
    let ψ' : ℝ → ℝ := fun t => fderiv ℝ J x s + c * t - fderiv ℝ J (γ t) s
    have hψ : ∀ t, HasDerivAt ψ (ψ' t) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => J x + fderiv ℝ J x s * t + c * t ^ 2 / 2)
          (fderiv ℝ J x s + c * t) t := by
        have := ((hasDerivAt_id t).const_mul (fderiv ℝ J x s)).const_add (J x)
        have h2 := (((hasDerivAt_id t).pow 2).const_mul c).div_const 2
        have key := this.add h2
        exact key.congr_deriv (by first | (simp; ring) | simp | ring | (norm_num; ring))
      exact h1.sub (hφ t)
    have hψ' : ∀ t, HasDerivAt ψ' (c - fderiv ℝ (fderiv ℝ J) (γ t) s s) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ J x s + c * t) c t := by
        simpa using ((hasDerivAt_id t).const_mul c).const_add (fderiv ℝ J x s)
      exact h1.sub (hφ' t)
    have hmono' : Monotone ψ' := by
      apply monotone_of_deriv_nonneg (fun t => (hψ' t).differentiableAt)
      intro t
      rw [(hψ' t).deriv]
      have := (hess (γ t) s).2
      rw [hc]; linarith
    have hψ'0 : ψ' 0 = 0 := by simp [ψ', γ]
    have hmonoψ : MonotoneOn ψ (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun t _ => (hψ t).continuousAt.continuousWithinAt
      · exact fun t _ => (hψ t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hψ t).deriv]
        have := hmono' (le_of_lt (Set.mem_Ioi.1 ht))
        linarith
    have h01 := hmonoψ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
    simp only [ψ, γ] at h01
    simp only [zero_smul, add_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div, sub_self, one_smul, mul_one, one_pow] at h01
    rw [hc] at h01
    linarith
  set v := gradient J (w k) with hv
  have hinner : ∀ s, inner ℝ v s = fderiv ℝ J (w k) s := by
    intro s
    simp [hv, gradient]
  have hn : ‖g k‖ ≥ 0 := norm_nonneg _
  have e1 : (1 - θ) * ‖g k‖ ^ 2 ≤ inner ℝ v (g k) := by
    have h1 : inner ℝ (g k - v) (g k) ≤ ‖g k - v‖ * ‖g k‖ := real_inner_le_norm _ _
    have h2 : inner ℝ (g k - v) (g k) = ‖g k‖ ^ 2 - inner ℝ v (g k) := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have h3 : ‖g k - v‖ * ‖g k‖ ≤ θ * ‖g k‖ * ‖g k‖ :=
      mul_le_mul_of_nonneg_right h48 (norm_nonneg _)
    nlinarith [h1, h2, h3]
  have e2 : ‖v‖ ≤ (1 + θ) * ‖g k‖ := by
    have h := abs_norm_sub_norm_le (g k) v
    have h' := abs_le.mp (h.trans h48)
    linarith [h'.1, h'.2]
  have hstep := descent (w k) (-(((1 - θ) / L) • g k))
  have e3 : w (k + 1) = w k + -(((1 - θ) / L) • g k) := by rw [hw k]; abel
  rw [e3]
  have e4 : fderiv ℝ J (w k) (-(((1 - θ) / L) • g k)) = -((1 - θ) / L) * inner ℝ v (g k) := by
    rw [← hinner]
    simp [inner_neg_right, inner_smul_right]
  have e5 : ‖-(((1 - θ) / L) • g k)‖ ^ 2 = ((1 - θ) / L) ^ 2 * ‖g k‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [e4, e5] at hstep
  have hβ : beta θ = (1 - θ) ^ 2 / (2 * (1 + θ) ^ 2) := rfl
  have e6 : ‖v‖ ^ 2 ≤ (1 + θ) ^ 2 * ‖g k‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) e2 2
  have h1θ : 0 < 1 - θ := by linarith
  have hθp : 0 < (1 + θ) ^ 2 := by positivity
  have e7 : beta θ / L * ‖v‖ ^ 2 ≤ (1 - θ) ^ 2 / (2 * L) * ‖g k‖ ^ 2 := by
    rw [hβ]
    have : (1 - θ) ^ 2 / (2 * (1 + θ) ^ 2) / L * ‖v‖ ^ 2 ≤
        (1 - θ) ^ 2 / (2 * (1 + θ) ^ 2) / L * ((1 + θ) ^ 2 * ‖g k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left e6
      positivity
    refine this.trans (le_of_eq ?_)
    field_simp
  have e8 : -((1 - θ) / L) * inner ℝ v (g k) ≤ -((1 - θ) / L) * ((1 - θ) * ‖g k‖ ^ 2) := by
    have : 0 ≤ (1 - θ) / L := by positivity
    nlinarith [e1]
  have e9 : L / 2 * (((1 - θ) / L) ^ 2 * ‖g k‖ ^ 2) = (1 - θ) ^ 2 / (2 * L) * ‖g k‖ ^ 2 := by
    field_simp
  have e10 : -((1 - θ) / L) * ((1 - θ) * ‖g k‖ ^ 2) = -((1 - θ) ^ 2 / L * ‖g k‖ ^ 2) := by
    field_simp
  have e11 : (1 - θ) ^ 2 / L * ‖g k‖ ^ 2 = 2 * ((1 - θ) ^ 2 / (2 * L) * ‖g k‖ ^ 2) := by
    field_simp
  linarith
