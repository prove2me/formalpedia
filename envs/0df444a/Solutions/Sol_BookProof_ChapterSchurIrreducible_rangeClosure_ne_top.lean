-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.rangeClosure_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:26:05.835335+00:00
-- url     : https://prove2.me/submissions/d48cfe03-5c7b-4cab-913f-441d8e1b1c70

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.rangeClosure_ne_top
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_le_ker
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {F G : V →L[ℂ] V} (hG : G ≠ 0) (h : G * F = 0) :
    rangeClosure F ≠ ⊤ := by

  intro htop
  apply hG
  ext x
  have hx : x ∈ rangeClosure F := by rw [htop]; trivial
  have := rangeClosure_le_ker h hx
  simpa using this
