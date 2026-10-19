-- Prove2me | solution 1 for GarrettFA.isQuasiComplete_pi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:06:12.949233+00:00
-- url     : https://prove2.me/submissions/b409647c-c569-4307-806d-9bacf50cab42

import Mathlib
import Definitions.Def_GarrettFA_IsQuasiComplete

universe u
open Topology

namespace GAPi
open GarrettFA

theorem main {𝕜 : Type*} [RCLike 𝕜] {ι : Type u}
    {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, T2Space (E i)]
    (hE : ∀ i, IsQuasiComplete 𝕜 (E i)) :
    IsQuasiComplete 𝕜 (∀ i, E i) := by
  classical
  intro I _ _ v hb hc
  have hne : Nonempty I := by
    obtain ⟨i₀, _⟩ := hc Set.univ Filter.univ_mem
    exact ⟨i₀⟩
  have hcomp : ∀ j, ∃ x : E j, ∀ N ∈ 𝓝 (0 : E j), ∃ i₀ : I, ∀ i ≥ i₀, v i j - x ∈ N := by
    intro j
    apply hE j I (fun k => v k j)
    · have := hb.image (ContinuousLinearMap.proj (R := 𝕜) (φ := E) j)
      have e : (ContinuousLinearMap.proj (R := 𝕜) (φ := E) j) '' Set.range v =
          Set.range (fun k => v k j) := by
        ext y; simp
      rw [e] at this
      exact this
    · intro N hN
      have hN' : (fun f : (∀ i, E i) => f j) ⁻¹' N ∈ 𝓝 (0 : ∀ i, E i) :=
        (continuous_apply j).continuousAt.preimage_mem_nhds (by simpa using hN)
      obtain ⟨i₀, h⟩ := hc _ hN'
      exact ⟨i₀, fun i hi k hk => by simpa using h i hi k hk⟩
  choose x hx using hcomp
  refine ⟨x, fun N hN => ?_⟩
  rw [nhds_pi, Filter.mem_pi'] at hN
  obtain ⟨F, t, ht, hsub⟩ := hN
  choose i₀ hi₀ using fun j : F => hx j (t j) (by simpa using ht j)
  obtain ⟨M, hM⟩ := Finset.exists_le (Finset.univ.image i₀)
  refine ⟨M, fun i hi => hsub ?_⟩
  intro j hj
  have := hi₀ ⟨j, hj⟩ i (le_trans (hM _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))) hi)
  simpa using this

end GAPi

open GarrettFA in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {ι : Type u}
    {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, T2Space (E i)]
    (hE : ∀ i, IsQuasiComplete 𝕜 (E i)) :
    IsQuasiComplete 𝕜 (∀ i, E i) :=
  GAPi.main hE
