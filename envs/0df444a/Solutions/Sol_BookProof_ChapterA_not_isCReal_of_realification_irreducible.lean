-- Prove2me | solution 1 for BookProof.ChapterA.not_isCReal_of_realification_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:28:00.994596+00:00
-- url     : https://prove2.me/submissions/34597d1c-be01-4dcb-bdfc-97d7b01c6261

-- Generated from ChapterA1f.lean — solution of BookProof.ChapterA.not_isCReal_of_realification_irreducible
import Mathlib
import Definitions.Def_ChapterA1f
import Theorems.Thm_BookProof_ChapterA_isCReal_realification_reducible
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial V] (M : System ℂ V)
    (h : (rxSystem M).IsIrreducible) : ¬ IsCReal M := fun hc => isCReal_realification_reducible M hc h
