-- Prove2me | solution 1 for BookProof.HermiteRelative.foOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:59.002781+00:00
-- url     : https://prove2.me/submissions/7442953d-3059-4304-83cc-f7dd9dedd979

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.foOp_symmetric
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_symmetricOn_of_polySym
import Theorems.Thm_BookProof_HermiteRelative_polySym_foPoly
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
theorem solution (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (foOp b b') := symmetricOn_of_polySym (polySym_foPoly b b')
