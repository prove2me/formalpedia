-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.momOp_apply_eq_differential
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:57:44.020423+00:00
-- url     : https://prove2.me/submissions/65f6cc43-4d09-46a9-aa74-b190d9e8a8d3

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.momOp_apply_eq_differential
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_hasDerivAt_pgFun_sec
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
    pgFun (momPoly i p) x
      = -Complex.I * deriv (fun t : ℝ => pgFun p (sec i x t)) (x i) := by

  rw [(hasDerivAt_pgFun_sec i p x).deriv]
  simp only [momPoly, pgFun, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.smul_eval]
  ring
