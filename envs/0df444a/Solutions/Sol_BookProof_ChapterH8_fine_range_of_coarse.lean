-- Prove2me | solution 1 for BookProof.ChapterH8.fine_range_of_coarse
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:52:57.568861+00:00
-- url     : https://prove2.me/submissions/118f90c2-8692-47ee-86d4-bcf904f1be02

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.fine_range_of_coarse
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
open BookProof.ChapterH8



open ContinuousLinearMap

noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vm ((adjoint Vm) v) = v := by

  set w : F := (adjoint Vn) v with hw
  have hvw : v = Vm (J w) := by rw [hJ] at hv; exact hv.symm
  have hmm : (adjoint Vm) (Vm (J w)) = J w :=
    congrArg (fun f : G →L[ℂ] G => f (J w)) hVm
  rw [hvw, hmm]
