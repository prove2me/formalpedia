-- Prove2me | solution 1 for BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:15:06.23134+00:00
-- url     : https://prove2.me/submissions/9ff97eeb-8d40-4769-80f3-1fb10156b051

-- Generated from ChapterUnitaryCompleteReducibility.lean — solution of BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility




open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊥ : Submodule ℂ V) := by

  intro g x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]
