-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.pgLp_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:08:25.248744+00:00
-- url     : https://prove2.me/submissions/dba90e31-ab0c-4e7b-8ef9-8c038dcd9922

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.pgLp_smul
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
theorem solution (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgLp (c • p) = c • pgLp p := map_smul (pgMap (d := d)) c p
