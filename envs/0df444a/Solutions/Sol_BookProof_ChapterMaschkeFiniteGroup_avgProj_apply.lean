-- Prove2me | solution 1 for BookProof.ChapterMaschkeFiniteGroup.avgProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:49:17.485128+00:00
-- url     : https://prove2.me/submissions/fc2dba5e-7f08-4445-91f5-221f71944847

-- Generated from ChapterMaschkeFiniteGroup.lean — solution of BookProof.ChapterMaschkeFiniteGroup.avgProj_apply
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup




variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (x : V) :
    avgProj ρ pi x = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g (pi (ρ g⁻¹ x)) := by

  simp [avgProj, LinearMap.sum_apply]
