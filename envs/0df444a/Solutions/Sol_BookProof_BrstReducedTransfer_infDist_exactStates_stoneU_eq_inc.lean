-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T18:57:51.442468+00:00
-- url     : https://prove2.me/submissions/89884d29-c35f-48bf-b73b-c8fbf1bf0b76

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Theorems.Thm_BookProof_BrstReducedTransfer_infDist_exactStates_eq_inc
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
open BookProof.BrstReducedTransfer




open BookProof BookProof.ChapterStoneResolvent




variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →L[ℂ] H)
variable (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y))

set_option maxHeartbeats 1000000 in
include hcomm in
theorem solution (t : ℝ) (x : H) :
    Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om) :=
  infDist_exactStates_eq_inc Om _ hcomm (by simp) (fun s t x => T.stoneU_apply_stoneU s t x)
      (fun s y => T.norm_stoneU_apply s y) t x