-- Prove2me | solution 1 for BookProof.NavierStokesFlow.matrixFlow_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:14.888186+00:00
-- url     : https://prove2.me/submissions/06ad3bac-1a57-4767-bc1f-954669253e98

-- Generated from ChapterNavierStokesCauchy.lean — solution of BookProof.NavierStokesFlow.matrixFlow_comm
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    matrixFlow A t * A = A * matrixFlow A t := (((Commute.refl A).smul_left t).exp_left).eq
