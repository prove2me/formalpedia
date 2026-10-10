-- Prove2me | solution 1 for BookProof.ChapterMaschkeFiniteGroup.avgProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:49:32.016436+00:00
-- url     : https://prove2.me/submissions/02c8be8e-eb4e-44f6-9eac-0bbf821fbc45

-- Generated from ChapterMaschkeFiniteGroup.lean — solution of BookProof.ChapterMaschkeFiniteGroup.avgProj_mem
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_apply
open BookProof.ChapterMaschkeFiniteGroup




variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x, pi x ∈ W) (x : V) : avgProj ρ pi x ∈ W := by

  rw [avgProj_apply]
  exact W.smul_mem _ (W.sum_mem fun g _ => hW g _ (hpi _))
