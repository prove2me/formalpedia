-- Prove2me | solution 1 for BookProof.HermiteRelative.oscOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:18.23622+00:00
-- url     : https://prove2.me/submissions/23754f82-5718-4b9c-b13e-586af300fe18

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.oscOp_eq
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_coreOp_add
import Theorems.Thm_BookProof_HermiteRelative_coreOp_smul
import Theorems.Thm_BookProof_HermiteRelative_coreOp_comp
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
open BookProof.HermiteRelative










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive
theorem solution (i : Fin d) :
    coreOp (oscPoly i) = (coreOp (momPoly i)).comp (coreOp (momPoly i))
      + (1/4 : ℂ) • ((coreOp (mulXPoly i)).comp (coreOp (mulXPoly i))) := by

  rw [oscPoly, coreOp_add, coreOp_comp, coreOp_smul, coreOp_comp]
