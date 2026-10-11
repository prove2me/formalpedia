-- Prove2me | solution 1 for BookProof.ChapterTrajectory.transProb_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:24.027674+00:00
-- url     : https://prove2.me/submissions/f105b72f-c2f4-4236-8756-25d88faabf57

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.transProb_sum
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (V : Matrix (Fin n) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (a : Fin n) : ∑ f, transProb V f a = 1 := by

  unfold transProb; simp [ ← Matrix.ext_iff ] at *;
  simp_all [ Matrix.mul_apply, Complex.normSq, Complex.sq_norm ];
  simp_all [ Complex.ext_iff, Matrix.one_apply ]
