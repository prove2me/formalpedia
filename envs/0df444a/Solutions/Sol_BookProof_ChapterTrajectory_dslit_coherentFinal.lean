-- Prove2me | solution 1 for BookProof.ChapterTrajectory.dslit_coherentFinal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:12.753261+00:00
-- url     : https://prove2.me/submissions/cdf12259-ccd2-460f-90a8-913feadc3d65

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.dslit_coherentFinal
import Mathlib
import Definitions.Def_ChapterTrajectory
import Theorems.Thm_BookProof_ChapterDoubleSlit_slit_open_born
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix
open BookProof.ChapterDoubleSlit


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution :
    coherentFinal H H psi0 0 = 1 ∧ coherentFinal H H psi0 1 = 0 := by
  have h := slit_open_born
  unfold coherentFinal
  rw [← Matrix.mulVec_mulVec]
  exact h
