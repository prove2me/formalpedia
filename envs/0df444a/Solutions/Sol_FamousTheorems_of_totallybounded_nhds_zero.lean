-- Prove2me | solution 1 for FamousTheorems.of_totallybounded_nhds_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:14.662247+00:00
-- url     : https://prove2.me/submissions/680c0531-b7fb-442d-b6cc-12dc45e894a3

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] 
    {Eᵤ : Type u_2} [inst_2 : AddCommGroup Eᵤ] [inst_3 : Module 𝕜 Eᵤ] [inst_4 : UniformSpace Eᵤ] [T2Space Eᵤ] 
    [IsUniformAddGroup Eᵤ] [ContinuousSMul 𝕜 Eᵤ] {U : Set Eᵤ}, U ∈ 𝓝 0 → TotallyBounded U → FiniteDimensional 𝕜 Eᵤ :=
  @_root_.FiniteDimensional.of_totallyBounded_nhds_zero
