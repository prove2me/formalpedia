-- Prove2me | solution 1 for BookProof.NavierStokesFlow.matrixFlow_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:13.576481+00:00
-- url     : https://prove2.me/submissions/34ff4e2a-9a55-4fb3-9203-e7fa90836cb3

-- Generated from ChapterNavierStokesCauchy.lean — solution of BookProof.NavierStokesFlow.matrixFlow_hasDerivAt
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (matrixFlow A) (matrixFlow A t * A) t := hasDerivAt_exp_smul_const (𝕂 := ℝ) A t
