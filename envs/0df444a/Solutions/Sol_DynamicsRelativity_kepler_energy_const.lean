-- Prove2me | solution 1 for DynamicsRelativity.kepler_energy_const
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:50:03.53023+00:00
-- url     : https://prove2.me/submissions/cde8aea9-9851-4a66-b13f-a87945734502

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


open DynamicsRelativity AMAux
theorem solution {k m : ℝ} {x : ℝ → Vec}
    (h : KeplerMotion k m x) (t₀ t₁ : ℝ) :
    keplerEnergy k m x t₀ = keplerEnergy k m x t₁ := by
  have hm := h.mass_pos
  have hx1 : Differentiable ℝ x := h.smooth.differentiable (by norm_num)
  have hv1 : Differentiable ℝ (vel x) := by
    have : ContDiff ℝ 1 (deriv x) := h.smooth.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hd : ∀ t, HasDerivAt (keplerEnergy k m x) 0 t := by
    intro t
    have hx0 : x t ≠ 0 := h.ne_origin t
    have hr : 0 < ‖x t‖ := norm_pos_iff.mpr hx0
    have hxd : HasDerivAt x (vel x t) t := (hx1 t).hasDerivAt
    have hvd : HasDerivAt (vel x) (acc x t) t := (hv1 t).hasDerivAt
    -- derivative of ‖v‖²
    have hv2 : HasDerivAt (fun s => ‖vel x s‖ ^ 2) (2 * inner ℝ (vel x t) (acc x t)) t := hvd.norm_sq
    -- derivative of ‖x‖ = √‖x‖²
    have hx2 : HasDerivAt (fun s => ‖x s‖ ^ 2) (2 * inner ℝ (x t) (vel x t)) t := hxd.norm_sq
    have hn : HasDerivAt (fun s => ‖x s‖) (2 * inner ℝ (x t) (vel x t) / (2 * ‖x t‖)) t := by
      have := hx2.sqrt (by positivity)
      simp only [Real.sqrt_sq (norm_nonneg _)] at this
      convert this using 2
    have hinv : HasDerivAt (fun s => k * m / ‖x s‖)
        (-(k * m) * (2 * inner ℝ (x t) (vel x t) / (2 * ‖x t‖)) / ‖x t‖ ^ 2) t := by
      have := (hn.inv hr.ne').const_mul (k * m)
      refine this.congr_deriv ?_
      ring
    have hE := (hv2.const_mul ((1 / 2) * m)).sub hinv
    have hfun : keplerEnergy k m x = fun s => (1 / 2) * m * ‖vel x s‖ ^ 2 - k * m / ‖x s‖ := by
      funext s; rfl
    rw [hfun]
    refine hE.congr_deriv ?_
    -- Newton: m a = -(k m / r³) x
    have heom := h.eom t
    simp only [keplerForce] at heom
    have key := congrArg (fun w => inner ℝ (vel x t) w) heom
    simp only [inner_smul_right] at key
    rw [real_inner_comm (vel x t) (x t),
      show (1 / 2 : ℝ) * m * (2 * inner ℝ (vel x t) (acc x t)) = m * inner ℝ (vel x t) (acc x t) by ring,
      key]
    field_simp
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t₀ t₁
