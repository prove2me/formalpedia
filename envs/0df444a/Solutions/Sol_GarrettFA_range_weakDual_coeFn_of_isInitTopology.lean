-- Prove2me | solution 1 for GarrettFA.range_weakDual_coeFn_of_isInitTopology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:49:56.467111+00:00
-- url     : https://prove2.me/submissions/054fdb4f-a29d-4fba-9ecd-64918d3c0a1b

import Mathlib
import Definitions.Def_GarrettFA_IsInitTopology

open Topology

namespace GAInit
open GarrettFA

theorem cont {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    (hV : IsInitTopology 𝕜 V) (f : V →ₗ[𝕜] 𝕜) :
    Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  set U : Set V := f ⁻¹' Metric.ball 0 ε
  have hbal : Balanced 𝕜 U := by
    intro a ha
    rintro _ ⟨x, hx, rfl⟩
    simp only [U, Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hx ⊢
    rw [map_smul, smul_eq_mul, norm_mul]
    calc ‖a‖ * ‖f x‖ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ < ε := by linarith
  have hconv : Convex ℝ U := by
    have : Convex ℝ (Metric.ball (0 : 𝕜) ε) := convex_ball 0 ε
    exact this.linear_preimage (f.restrictScalars ℝ)
  have hU := hV.mem_nhds_of_balanced_convex U hbal hconv (fun W hW => by
    have hc : Continuous (f.comp W.subtype) := LinearMap.continuous_of_finiteDimensional _
    have := hc.continuousAt (x := 0)
    rw [ContinuousAt] at this
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_zero, map_zero] at this
    exact this (Metric.ball_mem_nhds 0 hε))
  exact hU

end GAInit

open GarrettFA in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    (hV : IsInitTopology 𝕜 V) :
    Set.range (fun f : WeakDual 𝕜 V => (f : V → 𝕜)) = {g : V → 𝕜 | IsLinearMap 𝕜 g} := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨fun x y => map_add f x y, fun c x => map_smul f c x⟩
  · intro hg
    let f : V →ₗ[𝕜] 𝕜 := hg.mk' g
    exact ⟨(⟨f, GAInit.cont hV f⟩ : V →L[𝕜] 𝕜), rfl⟩
