-- Prove2me | solution 1 for BookProof.ChapterH8.compress_inv_transfer_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:52:46.356215+00:00
-- url     : https://prove2.me/submissions/f83c28f2-9cb3-4294-9d13-df7c65a0e34f

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.compress_inv_transfer_apply
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH4_compress_X_comp_V
import Theorems.Thm_BookProof_ChapterH4_compress_inv_transfer
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
theorem solution (V : F →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F)
    (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (hinv : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (v : E) (hv : V ((adjoint V) v) = v) :
    qXinv v = V (qBinv ((adjoint V) v)) := by

  have h := compress_inv_transfer V qX qXinv (compress V qX) qBinv
    (compress_X_comp_V V qX hVV hinv) hqXl hqBr
  have h2 := congrArg (fun f : F →L[ℂ] E => f ((adjoint V) v)) h
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at h2
  rw [hv] at h2
  exact h2
