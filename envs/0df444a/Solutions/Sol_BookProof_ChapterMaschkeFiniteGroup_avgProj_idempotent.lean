-- Prove2me | solution 1 for BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:52:18.266139+00:00
-- url     : https://prove2.me/submissions/e28ee357-8a71-4f06-b6fc-e1ceb47ca69d

-- Generated from ChapterMaschkeFiniteGroup.lean — solution of BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_mem
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_eq_self
open BookProof.ChapterMaschkeFiniteGroup




variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi_mem : ∀ x, pi x ∈ W)
    (hpi_id : ∀ x ∈ W, pi x = x) (x : V) :
    avgProj ρ pi (avgProj ρ pi x) = avgProj ρ pi x := avgProj_eq_self hW pi hpi_id (avgProj_mem hW pi hpi_mem x)
