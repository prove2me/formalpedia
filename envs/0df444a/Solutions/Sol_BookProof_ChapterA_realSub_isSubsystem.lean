-- Prove2me | solution 1 for BookProof.ChapterA.realSub_isSubsystem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:25:11.460542+00:00
-- url     : https://prove2.me/submissions/9c9947ad-b8cf-48e4-8e39-be62db5ca3ca

-- Generated from ChapterA1d.lean — solution of BookProof.ChapterA.realSub_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1d
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace




attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace V] (M : System ℂ V) {X : Submodule ℂ V}
    (hX : (M).IsSubsystem X) : (rxSystem M).IsSubsystem (realSub X) := by

  obtain ⟨hcl, hinv⟩ := hX
  refine ⟨?_, ?_⟩
  · convert hcl using 1 <;> (ext x; simp [mem_realSub])
  · rintro _ ⟨m, hm, rfl⟩ w hw
    rw [mem_realSub] at *
    exact hinv m hm w hw
