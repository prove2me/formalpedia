-- Prove2me | solution 1 for BookProof.ChapterMaschkeFiniteGroup.rho_rho
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:49:13.339485+00:00
-- url     : https://prove2.me/submissions/0859b7db-27e2-44a5-aabf-d388ef33a8e0

-- Generated from ChapterMaschkeFiniteGroup.lean — solution of BookProof.ChapterMaschkeFiniteGroup.rho_rho
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup




variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution (ρ : Representation ℂ G V) (a b : G) (x : V) :
    ρ a (ρ b x) = ρ (a * b) x := by

  rw [map_mul]; rfl
