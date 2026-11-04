-- Prove2me | solution 1 for BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T02:08:06.665325+00:00
-- url     : https://prove2.me/submissions/d60cc2de-7bac-41a5-a924-4f5761db0a88

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirk_end_to_end
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert
open BookProof.ChapterH4
open BookProof.ChapterH6
open BookProof.ChapterSirkEndToEnd

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}
variable {Fin' : Type*} [NormedAddCommGroup Fin'] [InnerProductSpace ℂ Fin'] [CompleteSpace Fin']

set_option maxHeartbeats 1000000 in
theorem solution
    (A : UnboundedSelfAdjoint E) (l t : ℝ)
    (V : Fin' →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : Fin' →L[ℂ] Fin')
    (p : Polynomial ℂ) (psiB : Fin' →L[ℂ] Fin') (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ Fin')
    (hViso : ∀ x : Fin', ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : Fin', ∃ y : Fin', A.resCLM l (V x) = V y)
    (hinvq : ∀ x : Fin', ∃ y : Fin', qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ Fin')
    (hcx1 : ‖A.stoneU t - (Polynomial.aeval (A.resCLM l) p).comp qXinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - (Polynomial.aeval (compress V (A.resCLM l)) p).comp qBinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖A.stoneU t v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m :=
  sirk_end_to_end V (A.resCLM l) qX qXinv qBinv p (A.stoneU t) (A.stoneU t) psiB C Dmin h m
      hVV hViso hVadj hinvX hinvq hqXl hqBr rfl hcx1 hcx2 v hv
