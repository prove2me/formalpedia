-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_apply
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:05:57.914741+00:00
-- url     : https://prove2.me/submissions/2d6f10d6-7bd2-4e2d-8d2f-afa5d2b271f0

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

theorem solution (mu : ℝ) (z : maxDom (velSym mu)) :
    diffMaxN mu (diffMaxEquiv mu z) = velUnitary ((diagMax (velSym mu) z : L2I Vel)) := by
  simp only [diffMaxN, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

#print axioms solution
