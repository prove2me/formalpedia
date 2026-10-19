-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:26:03.068059+00:00
-- url     : https://prove2.me/submissions/4ab7a686-9414-4cab-8ed1-7ca0dc776f64

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_mem_rangeClosure
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {F : V →L[ℂ] V} (hF : F ≠ 0) : rangeClosure F ≠ ⊥ := by

  intro h
  apply hF
  ext x
  have : F x ∈ rangeClosure F := mem_rangeClosure F x
  rw [h, Submodule.mem_bot] at this
  simp [this]
