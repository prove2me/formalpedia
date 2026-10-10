-- Prove2me | solution 1 for BookProof.ChapterMaschkeFiniteGroup.avgProj_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:51:53.992868+00:00
-- url     : https://prove2.me/submissions/e1c37fe2-3639-472b-8715-49f28215c514

-- Generated from ChapterMaschkeFiniteGroup.lean — solution of BookProof.ChapterMaschkeFiniteGroup.avgProj_comm
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_rho_rho
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_apply
open BookProof.ChapterMaschkeFiniteGroup




variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (h : G) (x : V) :
    avgProj ρ pi (ρ h x) = ρ h (avgProj ρ pi x) := by

  rw [avgProj_apply, avgProj_apply, map_smul]
  congr 1
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ ?_
  intro g
  simp only [Equiv.coe_mulLeft]
  have h1 : ρ g⁻¹ (ρ h x) = ρ (g⁻¹ * h) x := rho_rho ρ _ _ _
  have h2 : ρ h (ρ (h⁻¹ * g) (pi (ρ (h⁻¹ * g)⁻¹ x)))
      = ρ (h * (h⁻¹ * g)) (pi (ρ (h⁻¹ * g)⁻¹ x)) := rho_rho ρ _ _ _
  have h3 : h * (h⁻¹ * g) = g := by group
  have h4 : (h⁻¹ * g)⁻¹ = g⁻¹ * h := by group
  rw [h1, h2, h3, h4]
