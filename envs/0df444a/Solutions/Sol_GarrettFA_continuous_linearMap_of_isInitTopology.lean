-- Prove2me | solution 1 for GarrettFA.continuous_linearMap_of_isInitTopology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:49:48.565494+00:00
-- url     : https://prove2.me/submissions/cdb142d4-2608-4f32-9dad-df203ccfc23a

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
    (hV : IsInitTopology 𝕜 V) (f : V →ₗ[𝕜] 𝕜) :
    Continuous f := GAInit.cont hV f
