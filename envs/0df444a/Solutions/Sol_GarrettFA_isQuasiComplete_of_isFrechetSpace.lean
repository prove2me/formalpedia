-- Prove2me | solution 1 for GarrettFA.isQuasiComplete_of_isFrechetSpace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:48:52.727414+00:00
-- url     : https://prove2.me/submissions/154e0afa-aa2f-4a86-aa81-cd89f00c72b9

import Definitions.Def_GarrettFA_IsQuasiComplete
import Definitions.Def_GarrettFA_IsFrechetSpace

open Filter Topology GarrettFA

set_option autoImplicit false

theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : IsFrechetSpace 𝕜 X) :
    IsQuasiComplete 𝕜 X := by
  let : CompleteSpace X := hX.2.2
  intro I _ _ v _ hc
  obtain ⟨i₀, _⟩ := hc Set.univ univ_mem
  let : Nonempty I := ⟨i₀⟩
  have hcv : Cauchy (map v atTop) := by
    apply (IsUniformAddGroup.cauchy_map_iff_tendsto atTop v).2
    refine ⟨inferInstance, ?_⟩
    apply tendsto_def.2
    intro U hU
    obtain ⟨j₀, hj₀⟩ := hc U hU
    exact ((eventually_ge_atTop j₀).prod_mk (eventually_ge_atTop j₀)).mono
      (fun j hj => hj₀ j.1 hj.1 j.2 hj.2)
  obtain ⟨x, hx⟩ := cauchy_map_iff_exists_tendsto.1 hcv
  refine ⟨x, ?_⟩
  have ht : Tendsto (fun i => v i - x) atTop (𝓝 0) := by
    simpa only [sub_self] using hx.sub_const x
  intro U hU
  exact eventually_atTop.1 (ht hU)
