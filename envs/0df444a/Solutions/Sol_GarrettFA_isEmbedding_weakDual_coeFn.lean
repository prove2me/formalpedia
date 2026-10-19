-- Prove2me | solution 1 for GarrettFA.isEmbedding_weakDual_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:49:40.849347+00:00
-- url     : https://prove2.me/submissions/2ea9578c-ddb8-4247-bada-8d6a06f5699f

import Mathlib

theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    [LocallyConvexSpace ℝ V] :
    Topology.IsEmbedding (fun f : WeakDual 𝕜 V => (f : V → 𝕜)) ∧
      Set.range (fun f : WeakDual 𝕜 V => (f : V → 𝕜)) ⊆ {g : V → 𝕜 | IsLinearMap 𝕜 g} := by
  refine ⟨?_, ?_⟩
  · have hB : Function.Injective (topDualPairing 𝕜 V) := fun f g h =>
      ContinuousLinearMap.ext fun x => LinearMap.congr_fun h x
    exact WeakBilin.isEmbedding hB
  · rintro _ ⟨f, rfl⟩
    exact ⟨fun x y => map_add f x y, fun c x => map_smul f c x⟩
