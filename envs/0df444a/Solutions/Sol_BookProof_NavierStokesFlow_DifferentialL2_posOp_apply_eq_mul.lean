-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.posOp_apply_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:08:59.890331+00:00
-- url     : https://prove2.me/submissions/3c4ba8c9-b07c-4506-808e-915ceedff149

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.posOp_apply_eq_mul
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (mulXPoly i p) x = ((x i : ℝ) : ℂ) * pgFun p x := by

  simp [pgFun, mulXPoly]
  ring
