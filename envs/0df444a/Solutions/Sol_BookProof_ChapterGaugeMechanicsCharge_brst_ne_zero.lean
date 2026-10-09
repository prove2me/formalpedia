-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.brst_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:36:48.286198+00:00
-- url     : https://prove2.me/submissions/d4210e20-bc69-407a-8beb-493521634d81

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.brst_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
import Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_chargeQ_ne_zero
open BookProof
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution : brstOmega ≠ 0 := by

  intro h
  apply chargeQ_ne_zero
  have := congrFun (congrFun h 1) 0
  simpa [brstOmega, ChapterG.BRST] using this
