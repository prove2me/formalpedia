-- Prove2me | solution 1 for FlowCalculus.smooth_bijective_flow_has_smooth_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T22:04:06.553279+00:00
-- url     : https://prove2.me/submissions/fe5e9f04-de1a-489b-9256-11359d69feaf

import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Set Function
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hb : ∀ t, Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ∃ ρ : ℝ → V → V, (∀ t, ContDiff ℝ ∞ (ρ t)) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) := by
  classical
  letI := FiniteDimensional.complete ℝ V
  let e : ℝ → V ≃ V := fun t => Equiv.ofBijective (ψ t) (hb t)
  let ρ : ℝ → V → V := fun t => (e t).symm
  refine ⟨ρ, ?_, fun t y => (e t).symm_apply_apply y, fun t y => (e t).apply_symm_apply y⟩
  intro t
  have hs : ContDiff ℝ ∞ (ψ t) := hψ.comp (contDiff_const.prodMk contDiff_id)
  have hi := FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hd t
  apply contDiff_iff_contDiffAt.mpr
  intro z
  let y := ρ t z
  let D := fderiv ℝ (ψ t) y
  have hbij : Bijective D := ⟨hi y, LinearMap.surjective_of_injective (hi y)⟩
  let L : V ≃L[ℝ] V := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hf : HasFDerivAt (ψ t) (L : V →L[ℝ] V) y := (hs.differentiable (by simp) y).hasFDerivAt
  have hz : ψ t y = z := (e t).apply_symm_apply z
  have hlocal := hs.contDiffAt.to_localInverse hf (by simp)
  have heq : hs.contDiffAt.localInverse hf (by simp) =ᶠ[𝓝 z] ρ t := by
    have hr := (hs.contDiffAt.hasStrictFDerivAt' hf (by simp)).eventually_right_inverse
    rw [hz] at hr
    filter_upwards [hr] with w hw
    apply (hb t).injective
    exact hw.trans ((e t).apply_symm_apply w).symm
  rw [hz] at hlocal
  exact hlocal.congr_of_eventuallyEq heq.symm
