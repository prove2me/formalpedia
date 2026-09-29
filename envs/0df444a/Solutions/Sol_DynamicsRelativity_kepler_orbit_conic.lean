-- Prove2me | solution 1 for DynamicsRelativity.kepler_orbit_conic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:22:27.016002+00:00
-- url     : https://prove2.me/submissions/1376300b-3bea-4d0f-8fb3-558245e18986

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

namespace Ag4Aux_KeplerConic

noncomputable def crossLin : Vec →ₗ[ℝ] Vec →ₗ[ℝ] Vec :=
  LinearMap.mk₂ ℝ cross
    (fun a b c => by unfold cross; ext i; simp [map_add, LinearMap.add_apply])
    (fun r a b => by unfold cross; ext i; simp [map_smul, LinearMap.smul_apply])
    (fun a b c => by unfold cross; ext i; simp [map_add])
    (fun r a b => by unfold cross; ext i; simp [map_smul])

noncomputable def B : Vec →L[ℝ] Vec →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Vec →ₗ[ℝ] Vec) ≃ₗ[ℝ] (Vec →L[ℝ] Vec)).toLinearMap ∘ₗ crossLin)

lemma B_apply (a b : Vec) : B a b = cross a b := by
  simp [B, crossLin]

lemma cross_self' (a : Vec) : cross a a = 0 := by
  unfold cross; simp [cross_self]

lemma hasDerivAt_L {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t : ℝ) :
    HasDerivAt (angularMomentum m x) (m • cross (x t) (acc x t)) t := by
  have hx1 : Differentiable ℝ x := h.smooth.differentiable (by norm_num)
  have hv1 : Differentiable ℝ (vel x) := by
    have : ContDiff ℝ 1 (deriv x) := h.smooth.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hxd : HasDerivAt x (vel x t) t := (hx1 t).hasDerivAt
  have hvd : HasDerivAt (vel x) (acc x t) t := (hv1 t).hasDerivAt
  have hB := ContinuousLinearMap.hasDerivAt_of_bilinear (B := B) (fun _ => hxd) (fun _ => hvd)
  have hfun : angularMomentum m x = fun s => m • B (x s) (vel x s) := by
    funext s; simp [angularMomentum, B_apply]
  rw [hfun]
  have := hB.const_smul m
  refine this.congr_deriv ?_
  rw [B_apply, B_apply, cross_self', add_zero]


lemma L_const {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t₀ t₁ : ℝ) :
    angularMomentum m x t₀ = angularMomentum m x t₁ := by
  have hm := h.mass_pos
  have hzero : ∀ t, cross (x t) (acc x t) = 0 := by
    intro t
    have ha : acc x t = (m⁻¹ * (F ‖x t‖ / ‖x t‖)) • x t := by
      have := h.eom t
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
    rw [ha]; unfold cross; simp [WithLp.ofLp_smul, map_smul, cross_self]
  have hd : ∀ t, HasDerivAt (angularMomentum m x) 0 t := by
    intro t
    have := hasDerivAt_L h t
    rw [hzero, smul_zero] at this
    exact this
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t₀ t₁

lemma triple (a b c : Vec) : cross a (cross b c) = (inner ℝ a c) • b - (inner ℝ a b) • c := by
  unfold cross
  ext i; fin_cases i <;> simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

lemma scalar_triple (x v : Vec) : inner ℝ (cross v (cross x v)) x = ‖cross x v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma cross_smul_left' (s : ℝ) (a b : Vec) : cross (s • a) b = s • cross a b := by
  unfold cross
  ext i; fin_cases i <;> simp [cross_apply]

lemma conic_main {k m : ℝ} {x : ℝ → Vec} (hk : 0 < k) (h : KeplerMotion k m x) :
    ∀ t, ‖x t‖ + inner ℝ (k⁻¹ • cross (vel x 0) (cross (x 0) (vel x 0)) - ‖x 0‖⁻¹ • x 0) (x t)
      = ‖cross (x 0) (vel x 0)‖ ^ 2 / k := by
  have hm := h.mass_pos
  have hx1 : Differentiable ℝ x := h.smooth.differentiable (by norm_num)
  have hv1 : Differentiable ℝ (vel x) := by
    have : ContDiff ℝ 1 (deriv x) := h.smooth.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  set hc := cross (x 0) (vel x 0) with hhc
  have hct : ∀ t, cross (x t) (vel x t) = hc := by
    intro t
    have := L_const h t 0
    unfold angularMomentum at this
    exact smul_right_injective _ hm.ne' this
  let A : ℝ → Vec := fun t => k⁻¹ • cross (vel x t) hc - (‖x t‖⁻¹) • x t
  have hA : ∀ t, HasDerivAt A 0 t := by
    intro t
    have hr : 0 < ‖x t‖ := norm_pos_iff.mpr (h.ne_origin t)
    have hxd : HasDerivAt x (vel x t) t := (hx1 t).hasDerivAt
    have hvd : HasDerivAt (vel x) (acc x t) t := (hv1 t).hasDerivAt
    have hx2 : HasDerivAt (fun s => ‖x s‖ ^ 2) (2 * inner ℝ (x t) (vel x t)) t := hxd.norm_sq
    have hn : HasDerivAt (fun s => ‖x s‖) (2 * inner ℝ (x t) (vel x t) / (2 * ‖x t‖)) t := by
      have := hx2.sqrt (by positivity)
      simp only [Real.sqrt_sq (norm_nonneg _)] at this
      convert this using 2
    have hinv := hn.inv hr.ne'
    have hcr : HasDerivAt (fun s => cross (vel x s) hc) (cross (acc x t) hc) t := by
      have := (B.flip hc).hasFDerivAt.comp_hasDerivAt t hvd
      simp only [Function.comp_def, ContinuousLinearMap.flip_apply, B_apply] at this
      exact this
    have hAd := (hcr.const_smul k⁻¹).sub (hinv.smul hxd)
    refine hAd.congr_deriv ?_
    have ha : acc x t = (-k / ‖x t‖ ^ 3) • x t := by
      have := h.eom t
      simp only [keplerForce] at this
      rw [← inv_smul_smul₀ hm.ne' (acc x t), this, smul_smul]
      congr 1
      field_simp
    rw [ha, ← hct t, cross_smul_left', triple, real_inner_self_eq_norm_sq]
    simp only [Pi.inv_apply]
    match_scalars <;> field_simp <;> ring
  have hAconst : ∀ t, A t = A 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hA s).differentiableAt) (fun s => (hA s).deriv) t 0
  intro t
  show ‖x t‖ + inner ℝ (A 0) (x t) = _
  rw [← hAconst t]
  have hr : 0 < ‖x t‖ := norm_pos_iff.mpr (h.ne_origin t)
  show ‖x t‖ + inner ℝ (k⁻¹ • cross (vel x t) hc - ‖x t‖⁻¹ • x t) (x t) = _
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    ← hct t, scalar_triple]
  field_simp
  ring


lemma lagrange (a b : Vec) : ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - (inner ℝ a b) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma perp_left (a b : Vec) : inner ℝ a (cross a b) = 0 := by
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma perp_right (a b : Vec) : inner ℝ b (cross a b) = 0 := by
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma perp_right' (a b : Vec) : inner ℝ (cross a b) b = 0 := by
  rw [real_inner_comm]; exact perp_right a b

lemma normL {m : ℝ} {x : ℝ → Vec} (hm : 0 < m) :
    ‖angularMomentum m x 0‖ / m = ‖cross (x 0) (vel x 0)‖ := by
  unfold angularMomentum
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
  field_simp

end Ag4Aux_KeplerConic

open Ag4Aux_KeplerConic in
theorem solution {k m : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0) :
    ∃ A : Vec, ∀ t, ‖x t‖ + inner ℝ A (x t) =
      (‖angularMomentum m x 0‖ / m) ^ 2 / k := by
  refine ⟨k⁻¹ • cross (vel x 0) (cross (x 0) (vel x 0)) - ‖x 0‖⁻¹ • x 0, fun t => ?_⟩
  rw [conic_main hk h t, normL h.mass_pos]
