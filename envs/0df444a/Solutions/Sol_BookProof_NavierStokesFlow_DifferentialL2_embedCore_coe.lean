-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.embedCore_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:19:04.290163+00:00
-- url     : https://prove2.me/submissions/49800a96-ce6e-437a-bec1-02d92fee7184

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.embedCore_coe
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

set_option maxHeartbeats 1000000 in
theorem solution (x : lpFiniteModes Vel) :
    ((embedCore x : polyGaussCore (d := 3)) : L2d 3) = velUnitary ((x : L2I Vel)) := rfl
