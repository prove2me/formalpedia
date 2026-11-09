-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.lc2_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:50:49.109855+00:00
-- url     : https://prove2.me/submissions/b76dbd2c-7150-490c-9fdb-e6bf1574db51

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.lc2_shift
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
    lc2 (a + Finsupp.single i 2) i = rc2 a i := by
  rw [lc2, rc2]
  have h : ((a + Finsupp.single i 2 : Fin d →₀ ℕ) i : ℝ) = (a i : ℝ) + 2 := by
    simp
  rw [h]
  ring_nf
