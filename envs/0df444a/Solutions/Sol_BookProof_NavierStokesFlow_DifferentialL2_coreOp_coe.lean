-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.coreOp_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:25:33.615758+00:00
-- url     : https://prove2.me/submissions/5ed99226-470b-483c-a0df-e0f97c7b2bf7

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.coreOp_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreEquiv_coe
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coreEquiv
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
theorem solution (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ((coreOp T (coreEquiv p) : polyGaussCore (d := d)) : L2d d) = pgLp (T p) := by

  rw [coreOp_coreEquiv, coreEquiv_coe]
