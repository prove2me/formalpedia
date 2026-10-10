-- Prove2me | solution 1 for BookProof.ChapterLittleGroup.mem_littleGroup
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:39:06.087205+00:00
-- url     : https://prove2.me/submissions/2ca79d2f-b7f9-4ece-a678-beeed010d2b2

-- Generated from ChapterLittleGroup.lean — solution of BookProof.ChapterLittleGroup.mem_littleGroup
import Mathlib
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterLittleGroup




variable {G : Type*} [Group G] {K : Type*}

variable {G : Type*} [Group G] {K : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {q : K → G} {l₀ : K} {g : G} :
    g ∈ littleGroup q l₀ ↔ q l₀ * g = g * q l₀ := by

  rw [littleGroup, Subgroup.mem_centralizer_iff]
  constructor
  · intro h; exact h (q l₀) rfl
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy; exact h
