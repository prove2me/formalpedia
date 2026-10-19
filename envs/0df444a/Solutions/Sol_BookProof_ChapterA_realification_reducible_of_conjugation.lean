-- Prove2me | solution 1 for BookProof.ChapterA.realification_reducible_of_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:27:58.382061+00:00
-- url     : https://prove2.me/submissions/67a37fb6-c73d-4bcf-be7a-6d930fcf0f01

-- Generated from ChapterA1f.lean — solution of BookProof.ChapterA.realification_reducible_of_conjugation
import Mathlib
import Definitions.Def_ChapterA1f
import Theorems.Thm_BookProof_ChapterA_conjFixed_isSubsystem
import Theorems.Thm_BookProof_ChapterA_conjFixed_ne_bot
import Theorems.Thm_BookProof_ChapterA_conjFixed_ne_top
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial V] (M : System ℂ V)
    (θ : AntiUnitary V) (hθ : IsConjugation M θ) : ¬ (rxSystem M).IsIrreducible := by

  intro hirr
  rcases hirr (conjFixed θ) (conjFixed_isSubsystem M θ hθ) with h | h
  · exact conjFixed_ne_bot θ hθ.1 h
  · exact conjFixed_ne_top θ h
