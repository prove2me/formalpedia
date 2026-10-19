-- Prove2me | solution 1 for BookProof.ChapterA.cType_exhaustive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:28.380594+00:00
-- url     : https://prove2.me/submissions/65eefe13-6037-4511-84e6-1c3b7e68afaa

-- Generated from ChapterA1c.lean — solution of BookProof.ChapterA.cType_exhaustive
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) :
    IsCReal M ∨ IsCPseudoreal M ∨ IsCComplex M := by

  by_cases h1 : IsCReal M
  · exact Or.inl h1
  · by_cases h2 : HasCommutingAntiUnitary M
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr h2)
