-- Prove2me | solution 1 for BookProof.ChapterH8.compress_adjoint_intertwine_poly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:56:05.128572+00:00
-- url     : https://prove2.me/submissions/50da7abd-cdc3-4216-b8ce-dcc6ed1fd893

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.compress_adjoint_intertwine_poly
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_adjoint_compress
import Theorems.Thm_BookProof_ChapterH8_compress_aeval_comp_intertwine
import Theorems.Thm_BookProof_ChapterH8_adjoint_aeval
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH8



open ContinuousLinearMap

noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH4

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y) (p : Polynomial ℂ) :
    (adjoint J).comp (Polynomial.aeval (compress Vm X) p)
      = (Polynomial.aeval (compress Vn X) p).comp (adjoint J) := by

  have hpp : (p.map (starRingEnd ℂ)).map (starRingEnd ℂ) = p := by
    simp [Polynomial.map_map]
  have hstar := compress_aeval_comp_intertwine Vn Vm J (adjoint X) hJ hVm hJJ hinvadj
    (p.map (starRingEnd ℂ))
  have hadj := congrArg ContinuousLinearMap.adjoint hstar
  rw [adjoint_comp, adjoint_comp, adjoint_aeval, adjoint_aeval, adjoint_compress,
    adjoint_compress, adjoint_adjoint, hpp] at hadj
  exact hadj
