-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_band_refinement_rational
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:25:08.844354+00:00
-- url     : https://prove2.me/submissions/49c10e2f-4513-4ad1-8567-6c7132e7bec5

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_band_refinement_rational
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_adjoint_comp_self_of_nested
import Theorems.Thm_BookProof_ChapterH8_fine_range_of_coarse
import Theorems.Thm_BookProof_ChapterH8_compress_rational_transfer
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH4
open ContinuousLinearMap

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X qX qXinv : E →L[ℂ] E) (qBninv : F →L[ℂ] F) (qBminv : G →L[ℂ] G)
    (p : Polynomial ℂ) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y)
    (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y)
    (hqn : ∀ x : F, ∃ y : F, qX (Vn x) = Vn y)
    (hqm : ∀ x : G, ∃ y : G, qX (Vm x) = Vm y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBrn : (compress Vn qX).comp qBninv = ContinuousLinearMap.id ℂ F)
    (hqBrm : (compress Vm qX).comp qBminv = ContinuousLinearMap.id ℂ G)
    (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vm ((Polynomial.aeval (compress Vm X) p) (qBminv ((adjoint Vm) v)))
      = Vn ((Polynomial.aeval (compress Vn X) p) (qBninv ((adjoint Vn) v))) := by

  have hVn : (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F :=
    adjoint_comp_self_of_nested Vn Vm J hJ hVm hJJ
  have hvm : Vm ((adjoint Vm) v) = v := fine_range_of_coarse Vn Vm J hJ hVm v hv
  rw [← compress_rational_transfer Vm X qX qXinv qBminv p hVm hinvm hqm hqXl hqBrm v hvm,
    ← compress_rational_transfer Vn X qX qXinv qBninv p hVn hinvn hqn hqXl hqBrn v hv]
