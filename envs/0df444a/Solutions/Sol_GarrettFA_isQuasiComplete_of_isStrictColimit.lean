-- Prove2me | solution 1 for GarrettFA.isQuasiComplete_of_isStrictColimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:35:01.6525+00:00
-- url     : https://prove2.me/submissions/2f9bf887-e2e4-44e8-bfdf-64c431ed816f

import Mathlib
import Definitions.Def_GarrettFA_IsStrictColimit
import Definitions.Def_GarrettFA_IsQuasiComplete
import Theorems.Thm_GarrettFA_isVonNBounded_iff_of_isStrictColimit

open Topology Set Filter

theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] {F : ℕ → Submodule 𝕜 V} (hF : GarrettFA.IsStrictColimit 𝕜 F)
    (hq : ∀ n, GarrettFA.IsQuasiComplete 𝕜 (F n)) :
    GarrettFA.IsQuasiComplete 𝕜 V := by
  intro I _ _ v hbdd hC
  obtain ⟨n, hsub, hbn⟩ := (GarrettFA.isVonNBounded_iff_of_isStrictColimit hF (range v)).mp hbdd
  have hmem : ∀ i, v i ∈ F n := fun i => hsub ⟨i, rfl⟩
  let w : I → F n := fun i => ⟨v i, hmem i⟩
  have hrange : range w ⊆ {y : F n | (y : V) ∈ range v} := by
    rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩
  have hCw : ∀ N ∈ 𝓝 (0 : F n), ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, w i - w j ∈ N := by
    intro N hN
    rw [nhds_subtype, Filter.mem_comap] at hN
    obtain ⟨M, hM, hMN⟩ := hN
    obtain ⟨i₀, hi₀⟩ := hC M (by simpa using hM)
    exact ⟨i₀, fun i hi j hj => hMN (by simpa [w] using hi₀ i hi j hj)⟩
  obtain ⟨x, hx⟩ := hq n I w (hbn.subset hrange) hCw
  refine ⟨(x : V), fun N hN => ?_⟩
  have hN' : {y : F n | (y : V) ∈ N} ∈ 𝓝 (0 : F n) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨i₀, hi₀⟩ := hx _ hN'
  exact ⟨i₀, fun i hi => by simpa [w] using hi₀ i hi⟩
