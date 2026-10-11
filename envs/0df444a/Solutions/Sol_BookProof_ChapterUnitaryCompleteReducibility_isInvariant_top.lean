-- Prove2me | solution 1 for BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:14:52.285506+00:00
-- url     : https://prove2.me/submissions/ea51450c-54e5-4b50-ad61-1abc2f1e472a

-- Generated from ChapterUnitaryCompleteReducibility.lean — solution of BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility




open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊤ : Submodule ℂ V) := fun _ _ _ => trivial
