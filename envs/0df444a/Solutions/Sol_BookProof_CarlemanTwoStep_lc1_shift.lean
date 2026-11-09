-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.lc1_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:50:41.801388+00:00
-- url     : https://prove2.me/submissions/8a673245-ff18-40a1-a0d1-bf11eb3d592e

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.lc1_shift
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in

theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    lc1 (a + Finsupp.single i 1) i = rc1 a i := by
  rw [lc1, rc1]
  norm_num
