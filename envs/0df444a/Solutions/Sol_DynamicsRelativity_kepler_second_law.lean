-- Prove2me | solution 1 for DynamicsRelativity.kepler_second_law
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:50:02.819074+00:00
-- url     : https://prove2.me/submissions/15f564cf-9b9b-4227-a56a-7238d84e7fdb

import Mathlib
import Definitions.Def_DynamicsRelativity_CentralForces_Defs

namespace AMAux
open DynamicsRelativity

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

end AMAux


namespace AMAux2
open DynamicsRelativity AMAux

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
end AMAux2

open DynamicsRelativity AMAux AMAux2
theorem solution {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec}
    (h : CentralForceMotion m F x) (t₀ t₁ : ℝ) :
    sweptArea x t₀ t₁ = (‖angularMomentum m x 0‖ / m) / 2 * (t₁ - t₀) := by
  have hm := h.mass_pos
  have hc : ∀ t, ‖cross (x t) (vel x t)‖ = ‖angularMomentum m x 0‖ / m := by
    intro t
    rw [L_const h 0 t]
    unfold angularMomentum
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
    field_simp
  unfold sweptArea
  simp_rw [hc]
  simp
  ring
