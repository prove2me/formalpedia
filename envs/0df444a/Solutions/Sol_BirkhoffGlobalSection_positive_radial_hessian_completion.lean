-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_radial_hessian_completion
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T16:49:14.013341+00:00
-- url     : https://prove2.me/submissions/adbd67c1-f342-459b-ae14-e5970596e213

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Real.Basic

set_option Elab.async false

namespace BirkhoffGlobalSection.LocalHomogenization

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Projection to the tangent hyperplane along the radial direction. -/
noncomputable def tangentProjection (ell : E →ₗ[ℝ] ℝ) (x : E) : E →ₗ[ℝ] E :=
  LinearMap.id - (ell x)⁻¹ • ell.smulRight x

lemma tangentProjection_apply (ell : E →ₗ[ℝ] ℝ) (x v : E) :
    tangentProjection ell x v = v - (ell v / ell x) • x := by
  simp [tangentProjection, div_eq_inv_mul, mul_smul]

lemma projection_tangent (ell : E →ₗ[ℝ] ℝ) (x : E) (hr : ell x ≠ 0) (v : E) :
    ell (tangentProjection ell x v) = 0 := by
  rw [tangentProjection_apply, map_sub, map_smul]
  simp [smul_eq_mul, hr]

lemma projection_radial (ell : E →ₗ[ℝ] ℝ) (x : E) (hr : ell x ≠ 0) :
    tangentProjection ell x x = 0 := by
  rw [tangentProjection_apply]
  simp [hr]

lemma projection_eq_self (ell : E →ₗ[ℝ] ℝ) (x v : E) (hv : ell v = 0) :
    tangentProjection ell x v = v := by
  rw [tangentProjection_apply, hv]
  simp

/-- The canonical positive bilinear form associated to a positive tangent
Hessian and a positively transverse radial direction. -/
noncomputable def radialHomogenization (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (ell : E →ₗ[ℝ] ℝ) (x : E) : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :=
  B.compl₁₂ (tangentProjection ell x) (tangentProjection ell x) +
    (ell x)⁻¹ • LinearMap.mk₂ ℝ (fun v w => ell v * ell w)
      (by intros; simp [map_add, add_mul])
      (by intros; simp [map_smul, smul_eq_mul, mul_assoc])
      (by intros; simp [map_add, mul_add])
      (by intros; simp [map_smul, smul_eq_mul, mul_left_comm])

lemma radialHomogenization_apply (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (ell : E →ₗ[ℝ] ℝ) (x v w : E) :
    radialHomogenization B ell x v w =
      B (tangentProjection ell x v) (tangentProjection ell x w) + ell v * ell w / ell x := by
  simp [radialHomogenization, LinearMap.compl₁₂_apply, div_eq_inv_mul, mul_assoc, mul_left_comm]

lemma radial_identity (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (ell : E →ₗ[ℝ] ℝ) (x : E) (hr : ell x ≠ 0) (w : E) :
    radialHomogenization B ell x x w = ell w := by
  rw [radialHomogenization_apply, projection_radial ell x hr]
  simp [hr]

lemma tangent_identity (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (ell : E →ₗ[ℝ] ℝ) (x v w : E) (hv : ell v = 0) :
    radialHomogenization B ell x v w = B v w - (B v x / ell x) * ell w := by
  rw [radialHomogenization_apply, projection_eq_self ell x v hv, tangentProjection_apply]
  simp only [map_sub, map_smul, smul_eq_mul, hv, zero_mul, zero_div, add_zero]
  simp only [div_eq_mul_inv]
  ac_rfl

lemma same_tangent_restriction (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (ell : E →ₗ[ℝ] ℝ) (x v w : E) (hv : ell v = 0) (hw : ell w = 0) :
    radialHomogenization B ell x v w = B v w := by
  rw [tangent_identity B ell x v w hv, hw]
  simp

lemma symmetric (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (hB : ∀ v w, B v w = B w v) (ell : E →ₗ[ℝ] ℝ) (x : E) :
    ∀ v w, radialHomogenization B ell x v w = radialHomogenization B ell x w v := by
  intro v w
  rw [radialHomogenization_apply, radialHomogenization_apply, hB]
  rw [mul_comm (ell v) (ell w)]

lemma positive (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (ell : E →ₗ[ℝ] ℝ) (x : E) (hr : 0 < ell x)
    (hB : ∀ v : E, ell v = 0 → v ≠ 0 → 0 < B v v) :
    ∀ v : E, v ≠ 0 → 0 < radialHomogenization B ell x v v := by
  intro v hv
  rw [radialHomogenization_apply]
  have hp := projection_tangent ell x hr.ne' v
  have hn : 0 ≤ ell v * ell v / ell x := div_nonneg (mul_self_nonneg _) hr.le
  by_cases hP : tangentProjection ell x v = 0
  · have he : ell v ≠ 0 := by
      intro he
      rw [projection_eq_self ell x v he] at hP
      exact hv hP
    have hq : 0 < ell v * ell v / ell x := div_pos (mul_self_pos.mpr he) hr
    simpa [hP] using hq
  · exact add_pos_of_pos_of_nonneg (hB _ hp hP) hn

/-- On tangent directions the two associated Hamiltonian linear systems differ
only by a multiple of the Hamiltonian vector. -/
lemma shear_identity (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ)) (ell : E →ₗ[ℝ] ℝ)
    (x v : E) (hv : ell v = 0) {F : Type*} [AddCommGroup F] [Module ℝ F]
    (J : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] F) :
    J (radialHomogenization B ell x v) = J (B v) - (B v x / ell x) • J ell := by
  have h : radialHomogenization B ell x v = B v - (B v x / ell x) • ell := by
    ext w
    simpa using tangent_identity B ell x v w hv
  rw [h, map_sub, map_smul]

lemma quotient_identity (B : (E →ₗ[ℝ] E →ₗ[ℝ] ℝ)) (ell : E →ₗ[ℝ] ℝ)
    (x v : E) (hv : ell v = 0) {F G : Type*}
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (J : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] F) (L : F →ₗ[ℝ] G) (hL : L (J ell) = 0) :
    L (J (radialHomogenization B ell x v)) = L (J (B v)) := by
  rw [shear_identity B ell x v hv J, map_sub, map_smul, hL, smul_zero, sub_zero]

end BirkhoffGlobalSection.LocalHomogenization

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ell : E →ₗ[ℝ] ℝ) (x : E)
    (hr : 0 < ell x) (hBsym : ∀ v w, B v w = B w v)
    (hBpos : ∀ v : E, ell v = 0 → v ≠ 0 → 0 < B v v) :
    ∃ S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ,
      (∀ v w, S v w = S w v) ∧
      (∀ v : E, v ≠ 0 → 0 < S v v) ∧
      (∀ w, S x w = ell w) ∧
      (∀ v w, ell v = 0 → S v w = B v w - (B v x / ell x) * ell w) ∧
      (∀ v w, S v w =
        B (v - (ell v / ell x) • x) (w - (ell w / ell x) • x) +
          ell v * ell w / ell x) := by
  refine ⟨BirkhoffGlobalSection.LocalHomogenization.radialHomogenization B ell x,
    BirkhoffGlobalSection.LocalHomogenization.symmetric B hBsym ell x,
    BirkhoffGlobalSection.LocalHomogenization.positive B ell x hr hBpos,
    BirkhoffGlobalSection.LocalHomogenization.radial_identity B ell x hr.ne', ?_, ?_⟩
  · intro v w hv
    exact BirkhoffGlobalSection.LocalHomogenization.tangent_identity B ell x v w hv
  · intro v w
    rw [BirkhoffGlobalSection.LocalHomogenization.radialHomogenization_apply,
      BirkhoffGlobalSection.LocalHomogenization.tangentProjection_apply,
      BirkhoffGlobalSection.LocalHomogenization.tangentProjection_apply]
