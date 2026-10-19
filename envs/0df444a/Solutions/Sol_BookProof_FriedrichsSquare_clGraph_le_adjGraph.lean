-- Prove2me | solution 1 for BookProof.FriedrichsSquare.clGraph_le_adjGraph
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:09:19.902423+00:00
-- url     : https://prove2.me/submissions/5f837b6f-0627-47ca-a04f-8fd7f5484ac5

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.clGraph_le_adjGraph
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_ClosureUniqueness_mem_adjGraph_iff
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.ClosureUniqueness
open BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) :
    clGraph A ≤ adjGraph A := by

  intro p hp
  rw [mem_adjGraph_iff]
  intro v
  have h := clGraph_inner hsym hp v
  have h' := congrArg (starRingEnd ℂ) h
  rw [inner_conj_symm, inner_conj_symm] at h'
  exact h'.symm
