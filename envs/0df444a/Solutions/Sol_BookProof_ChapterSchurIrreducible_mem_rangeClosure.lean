-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.mem_rangeClosure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:26:00.332292+00:00
-- url     : https://prove2.me/submissions/eafda994-060f-403a-a2a5-638f5e766c4a

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.mem_rangeClosure
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (F : V →L[ℂ] V) (x : V) : F x ∈ rangeClosure F := Submodule.le_topologicalClosure _ ⟨x, rfl⟩
