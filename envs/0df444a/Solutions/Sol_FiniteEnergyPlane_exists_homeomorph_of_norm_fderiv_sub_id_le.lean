-- Prove2me | solution 1 for FiniteEnergyPlane.exists_homeomorph_of_norm_fderiv_sub_id_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T09:17:45.90527+00:00
-- url     : https://prove2.me/submissions/75a8c41f-d79d-4157-9ed2-c74ae650acdf

import Mathlib



/-!
# A2, abstract part 1: a smooth map with `‖Dψ - id‖ ≤ 1/2` is a smooth diffeomorphism
-/

namespace FiniteEnergyPlane

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

lemma dga2_lip (ψ : E → E) (hψ : ContDiff ℝ ∞ ψ)
    (hD : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (x y : E) :
    ‖ψ x - ψ y - (x - y)‖ ≤ 1 / 2 * ‖x - y‖ := by
  have hdiff : ∀ z, DifferentiableAt ℝ ψ z := fun z => (hψ.differentiable (by simp)) z
  have hg : ∀ z ∈ (univ : Set E), DifferentiableAt ℝ (fun x => ψ x - x) z :=
    fun z _ => (hdiff z).sub differentiableAt_id
  have hb : ∀ z ∈ (univ : Set E), ‖fderiv ℝ (fun x => ψ x - x) z‖ ≤ 1 / 2 := by
    intro z _
    have e : fderiv ℝ (fun x => ψ x - x) z = fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E :=
      ((hdiff z).hasFDerivAt.sub (hasFDerivAt_id z)).fderiv
    rw [e]
    exact hD z
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le hg hb (mem_univ y) (mem_univ x)
  have e : ψ x - x - (ψ y - y) = ψ x - ψ y - (x - y) := by abel
  rw [e] at this
  exact this

lemma dga2_norm_ge (ψ : E → E)
    (hD : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (z h : E) :
    1 / 2 * ‖h‖ ≤ ‖fderiv ℝ ψ z h‖ := by
  have h1 : ‖(fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E) h‖ ≤ 1 / 2 * ‖h‖ :=
    ((fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (hD z) (norm_nonneg h))
  have e : (fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E) h = fderiv ℝ ψ z h - h := by simp
  rw [e] at h1
  have := norm_sub_norm_le h (h - fderiv ℝ ψ z h)
  rw [sub_sub_cancel] at this
  rw [norm_sub_rev] at h1
  linarith

/-- The derivative of `ψ` at `z` as a continuous linear equivalence. -/
noncomputable def dga2_equiv (ψ : E → E)
    (hD : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (z : E) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ ψ z : E →ₗ[ℝ] E) (by
    intro a b hab
    have hab' : fderiv ℝ ψ z (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    have := dga2_norm_ge ψ hD z (a - b)
    rw [hab', norm_zero] at this
    have : ‖a - b‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this))).toContinuousLinearEquiv

lemma dga2_equiv_coe (ψ : E → E)
    (hD : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (z : E) :
    ((dga2_equiv ψ hD z : E ≃L[ℝ] E) : E →L[ℝ] E) = fderiv ℝ ψ z := by
  ext h; rfl

/-- A smooth self-map of a finite-dimensional real normed space whose derivative is everywhere
within `1/2` of the identity in operator norm is a homeomorphism with smooth inverse. -/
theorem exists_homeomorph_of_norm_fderiv_sub_id_le_aux (ψ : E → E) (hψ : ContDiff ℝ ∞ ψ)
    (hD : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ∃ e : E ≃ₜ E, (⇑e = ψ) ∧ ContDiff ℝ ∞ (e.symm : E → E) := by
  have hA : ApproximatesLinearOn ψ
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) univ (1 / 2 : NNReal) := by
    intro x _ y _
    have := dga2_lip ψ hψ hD x y
    simpa using this
  have hc : Subsingleton E ∨ (1 / 2 : NNReal) <
      ‖(((ContinuousLinearEquiv.refl ℝ E).symm : E ≃L[ℝ] E) : E →L[ℝ] E)‖₊⁻¹ := by
    right
    have : ‖(((ContinuousLinearEquiv.refl ℝ E).symm : E ≃L[ℝ] E) : E →L[ℝ] E)‖₊ = 1 := by
      simp
    rw [this, inv_one]
    exact NNReal.half_lt_self one_ne_zero
  refine ⟨hA.toHomeomorph ψ hc, rfl, ?_⟩
  have hdiff : ∀ z, DifferentiableAt ℝ ψ z := fun z => (hψ.differentiable (by simp)) z
  exact (hA.toHomeomorph ψ hc).contDiff_symm (f₀' := dga2_equiv ψ hD)
    (fun a => by rw [dga2_equiv_coe]; exact (hdiff a).hasFDerivAt) hψ

end FiniteEnergyPlane

open FiniteEnergyPlane

open Set
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] (ψ : E → E) (hψ : ContDiff ℝ ∞ ψ)
    (hD : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ∃ e : E ≃ₜ E, (⇑e = ψ) ∧ ContDiff ℝ ∞ (e.symm : E → E) :=
  exists_homeomorph_of_norm_fderiv_sub_id_le_aux ψ hψ hD
