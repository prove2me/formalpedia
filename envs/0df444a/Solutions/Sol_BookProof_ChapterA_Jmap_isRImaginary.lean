-- Prove2me | solution 1 for BookProof.ChapterA.Jmap_isRImaginary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:36.641719+00:00
-- url     : https://prove2.me/submissions/d5ed0579-35af-49aa-8a1d-36e75a000e0c

-- Generated from ChapterA1d.lean — solution of BookProof.ChapterA.Jmap_isRImaginary
import Mathlib
import Definitions.Def_ChapterA1d
import Theorems.Thm_BookProof_ChapterA_Jmap_sq
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace
open BookProof.ChapterA.AntiUnitary




attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace V] (M : System ℂ V) :
    IsRImaginary (rxSystem M) Jmap := by

  refine ⟨Jmap_sq, ?_⟩
  rintro _ ⟨m, hm, rfl⟩ x
  change (Complex.I : ℂ) • (m x) = m ((Complex.I : ℂ) • x)
  rw [map_smul]
