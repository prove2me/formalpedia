-- Prove2me | solution 1 for CubicNewton.GradDom.taylor_grad_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:07:02.958185+00:00
-- url     : https://prove2.me/submissions/4861c4b4-4820-4794-b48b-10baa3784f51

import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

theorem aux_tgb_main {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F)
    (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ F) :
    ‖g y - g x - H x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • v
  let ψ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => g (γ t) - g x - t • H x v
  have hγF : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ F := fun t ht =>
    hF_convex.add_smul_sub_mem hx hy ht
  have hγd : ∀ t : ℝ, HasDerivAt γ v t := by
    intro t
    have h := ((hasDerivAt_id' t).smul_const v).const_add x
    rw [one_smul] at h
    exact h
  have hψd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (H (γ t) v - H x v) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => g (γ s)) (H (γ t) v) t :=
      (hg (γ t) (hγF t ht)).comp_hasDerivAt t (hγd t)
    have h2 : HasDerivAt (fun s : ℝ => s • H x v) ((1:ℝ) • H x v) t :=
      (hasDerivAt_id t).smul_const (H x v)
    simp only [one_smul] at h2
    exact (h1.sub_const (g x)).sub h2
  have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun t ht =>
    (hψd t ht).continuousAt.continuousWithinAt
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := ψ) (a := 0) (b := 1) (f' := fun t => H (γ t) v - H x v)
    (B := fun t => L / 2 * t ^ 2 * ‖v‖ ^ 2) (B' := fun t => L * t * ‖v‖ ^ 2)
    hcont
    (fun t ht => (hψd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [ψ, γ])
    (by
      intro t
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring)
    (by
      intro t ht
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := Set.Ico_subset_Icc_self ht
      have h0 : 0 ≤ t := ht.1
      calc ‖H (γ t) v - H x v‖ = ‖(H (γ t) - H x) v‖ := by
            rw [ContinuousLinearMap.sub_apply]
        _ ≤ ‖H (γ t) - H x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L * ‖γ t - x‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (hLip _ (hγF t ht') _ hx) (norm_nonneg _)
        _ = L * t * ‖v‖ ^ 2 := by
            simp only [γ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
            ring)
  have h1 := key (x := 1) ⟨zero_le_one, le_rfl⟩
  have hψ1 : ψ 1 = g y - g x - H x (y - x) := by
    simp [ψ, γ, hv]
  rw [hψ1] at h1
  calc _ ≤ _ := h1
    _ = 1 / 2 * L * ‖y - x‖ ^ 2 := by rw [hv]; ring

end CubicNewton.GradDom

open CubicNewton.GradDom
open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ F, ∀ y ∈ F, ‖g y - g x - H x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := by
  intro x hx y hy
  exact aux_tgb_main F g H L hF_convex hg hLip x hx y hy
