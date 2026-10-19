-- Prove2me | solution 1 for BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:25:26.776988+00:00
-- url     : https://prove2.me/submissions/b929646f-8e07-4983-829d-b1f0a03b3e34

-- Generated from ChapterA1d.lean — solution of BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem
import Mathlib
import Definitions.Def_ChapterA1d
import Theorems.Thm_BookProof_ChapterA_realSub_isSubsystem
import Theorems.Thm_BookProof_ChapterA_cplxSub_isSubsystem
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace




attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace V] (M : System ℂ V) :
    M.IsIrreducible ↔
      ∀ Y : Submodule ℝ V, (rxSystem M).IsSubsystem Y →
        (∀ y ∈ Y, Jmap y ∈ Y) → Y = ⊥ ∨ Y = ⊤ := by

  constructor
  · intro hirr Y hY hYJ
    have hJ : ∀ y ∈ Y, (Complex.I : ℂ) • y ∈ Y := hYJ
    rcases hirr (cplxSub Y hJ) (cplxSub_isSubsystem M hJ hY) with h | h
    · exact Or.inl <| by
        have := congrArg realSub h
        rwa [realSub_cplxSub, realSub_bot] at this
    · exact Or.inr <| by
        have := congrArg realSub h
        rwa [realSub_cplxSub, realSub_top] at this
  · intro h X hX
    rcases h (realSub X) (realSub_isSubsystem M hX) (realSub_Jinvariant X) with h | h
    · refine Or.inl ?_
      ext x
      have hx := SetLike.ext_iff.mp h x
      rw [mem_realSub] at hx
      simpa using hx
    · refine Or.inr ?_
      ext x
      have hx := SetLike.ext_iff.mp h x
      rw [mem_realSub] at hx
      simpa using hx
