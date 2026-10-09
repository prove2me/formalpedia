-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.brst_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:36:34.334332+00:00
-- url     : https://prove2.me/submissions/c1972a4e-8c19-4bf5-8418-d587cffb0861

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.brst_nilpotent
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
import Theorems.Thm_BookProof_ChapterG_BRST_nilpotent
import Theorems.Thm_BookProof_ChapterG_BRST_nilpotent
import Theorems.Thm_BookProof_ChapterG_BRST_nilpotent
import Theorems.Thm_BookProof_ChapterG_BRST_nilpotent
open BookProof
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution : brstOmega * brstOmega = 0 := ChapterG.BRST_nilpotent chargeQ
