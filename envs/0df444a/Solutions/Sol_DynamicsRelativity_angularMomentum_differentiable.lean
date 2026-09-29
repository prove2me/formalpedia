-- Prove2me | solution 1 for DynamicsRelativity.angularMomentum_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:40:29.5229+00:00
-- url     : https://prove2.me/submissions/5ae3ff8a-a2a6-4edd-a6cb-4c7ad6168317

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
theorem solution {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) :
    Differentiable ℝ (angularMomentum m x) :=
  fun t => (hasDerivAt_L h t).differentiableAt
