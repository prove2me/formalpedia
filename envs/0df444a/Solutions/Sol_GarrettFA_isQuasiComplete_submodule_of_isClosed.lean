-- Prove2me | solution 1 for GarrettFA.isQuasiComplete_submodule_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:53:03.082996+00:00
-- url     : https://prove2.me/submissions/bb0fb028-837e-430f-849d-4b50edbdd177

import Mathlib
import Definitions.Def_GarrettFA_IsQuasiComplete

open Topology Filter

open GarrettFA in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    (hV : IsQuasiComplete 𝕜 V) (W : Submodule 𝕜 V) (hW : IsClosed (W : Set V)) :
    IsQuasiComplete 𝕜 W := by
  intro I _ _ v hb hv
  set u : I → V := fun i => (v i : V)
  have hub : Bornology.IsVonNBounded 𝕜 (Set.range u) := by
    have := hb.image W.subtypeL
    rwa [← Set.range_comp] at this
  have huc : ∀ N ∈ 𝓝 (0 : V), ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, u i - u j ∈ N := by
    intro N hN
    have : (W.subtype : W → V) ⁻¹' N ∈ 𝓝 (0 : W) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hN)
    obtain ⟨i₀, hi₀⟩ := hv _ this
    exact ⟨i₀, fun i hi j hj => hi₀ i hi j hj⟩
  obtain ⟨x, hx⟩ := hV I u hub huc
  have hxW : x ∈ (W : Set V) := by
    rw [← hW.closure_eq, mem_closure_iff_nhds]
    intro t ht
    have : (fun y => y + x) ⁻¹' t ∈ 𝓝 (0 : V) :=
      (continuous_add_const x).continuousAt.preimage_mem_nhds (by simpa using ht)
    obtain ⟨i₀, hi₀⟩ := hx _ this
    have := hi₀ i₀ le_rfl
    simp only [Set.mem_preimage, sub_add_cancel] at this
    exact ⟨u i₀, this, (v i₀).2⟩
  refine ⟨⟨x, hxW⟩, fun N hN => ?_⟩
  rw [mem_nhds_subtype] at hN
  obtain ⟨N', hN', hsub⟩ := hN
  obtain ⟨i₀, hi₀⟩ := hx N' (by simpa using hN')
  exact ⟨i₀, fun i hi => hsub (by simpa [u] using hi₀ i hi)⟩
