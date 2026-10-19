-- Prove2me | solution 1 for BookProof.ChapterA.conjFixed_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:27:14.592265+00:00
-- url     : https://prove2.me/submissions/4d98a40c-f14e-4f09-a7e6-50730755d77a

-- Generated from ChapterA1f.lean — solution of BookProof.ChapterA.conjFixed_invariant
import Mathlib
import Definitions.Def_ChapterA1f
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) :
    ∀ m ∈ (rxSystem M).ops, ∀ w ∈ conjFixed θ, m w ∈ conjFixed θ := by

  rintro _ ⟨m, hm, rfl⟩ w hw
  rw [mem_conjFixed] at *
  change θ (m w) = m w
  rw [hθ.2 m hm w, hw]
