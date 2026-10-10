-- Prove2me | solution 1 for BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:53:00.749105+00:00
-- url     : https://prove2.me/submissions/9750a0d5-e05a-4ff4-84d2-c385b9e42ca4

-- Generated from ChapterMaschkeFiniteGroup.lean — solution of BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_mem
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_eq_self
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_comm
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_range_eq_W
open BookProof.ChapterMaschkeFiniteGroup




variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : IsInvariant ρ W) :
    ∃ (W' : Submodule ℂ V) (p : V →ₗ[ℂ] V),
      IsInvariant ρ W' ∧ IsCompl W W' ∧ (∀ x, p (p x) = p x) ∧
        LinearMap.range p = W ∧ LinearMap.ker p = W' ∧
        (∀ (g : G) (x : V), p (ρ g x) = ρ g (p x)) := by

  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨W₀, hW₀⟩ := Submodule.exists_isCompl W
  set pi : V →ₗ[ℂ] V := W.subtype ∘ₗ W.projectionOnto W₀ hW₀ with hpidef
  have hpi_mem : ∀ x, pi x ∈ W := fun x => (W.projectionOnto W₀ hW₀ x).2
  have hpi_id : ∀ x ∈ W, pi x = x := by
    intro x hx
    have h : W.projectionOnto W₀ hW₀ x = ⟨x, hx⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hW₀ hx
    simp [hpidef, h]
  set p : V →ₗ[ℂ] V := avgProj ρ pi with hpdef
  have hp_mem : ∀ x, p x ∈ W := avgProj_mem hW pi hpi_mem
  have hp_id : ∀ x ∈ W, p x = x := fun x hx => avgProj_eq_self hW pi hpi_id hx
  have hp_comm : ∀ (g : G) (x : V), p (ρ g x) = ρ g (p x) := avgProj_comm ρ pi
  refine ⟨LinearMap.ker p, p, ?_, ?_, ?_, ?_, rfl, hp_comm⟩
  · intro g x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [hp_comm g x, hx, map_zero]
  · constructor
    · rw [disjoint_iff_inf_le]
      intro x hx
      have hx2 : p x = 0 := hx.2
      rw [hp_id x hx.1] at hx2
      simp [hx2]
    · rw [codisjoint_iff_le_sup]
      intro x _
      have hpx : p x ∈ W := hp_mem x
      have hker : x - p x ∈ LinearMap.ker p := by
        simp only [LinearMap.mem_ker, map_sub]
        rw [hp_id _ hpx, sub_self]
      have hsplit : x = p x + (x - p x) := by abel
      rw [hsplit]
      exact Submodule.add_mem_sup hpx hker
  · exact fun x => hp_id _ (hp_mem x)
  · exact avgProj_range_eq_W hW pi hpi_mem hpi_id
