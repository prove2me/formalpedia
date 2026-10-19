-- Prove2me | solution 1 for BookProof.ChapterA.IsCReal.hasCommutingAntiUnitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:26.695348+00:00
-- url     : https://prove2.me/submissions/2cb60421-a18d-4829-af00-4bcaeb631eaa

-- Generated from ChapterA1c.lean — solution of BookProof.ChapterA.IsCReal.hasCommutingAntiUnitary
import Mathlib
import Definitions.Def_ChapterA1c
import Theorems.Thm_BookProof_ChapterA_IsConjugation_commutesAntiUnitary
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace
open BookProof.ChapterA.AntiUnitary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} (h : IsCReal M) :
    HasCommutingAntiUnitary M := by

  obtain ⟨θ, hθ⟩ := h
  exact ⟨θ, hθ.commutesAntiUnitary⟩
