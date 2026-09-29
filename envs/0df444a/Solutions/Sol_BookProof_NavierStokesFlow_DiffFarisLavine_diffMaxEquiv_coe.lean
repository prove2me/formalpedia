-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxEquiv_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:42:50.750728+00:00
-- url     : https://prove2.me/submissions/1948d8e4-4b61-45a0-9186-8be0953dae30

import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2
noncomputable section
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem solution (mu : ℝ) (z : maxDom (velSym mu)) :
    ((diffMaxEquiv mu z : diffMaxDom mu) : L2d 3) = velUnitary ((z : L2I Vel)) := by
  rfl
