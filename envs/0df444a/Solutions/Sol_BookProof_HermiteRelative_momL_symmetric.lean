-- Prove2me | solution 1 for BookProof.HermiteRelative.momL_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:53.835527+00:00
-- url     : https://prove2.me/submissions/dc575911-ef19-4ae5-ad3a-094ae8db63c5

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.momL_symmetric
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_polySym_momPoly
import Theorems.Thm_BookProof_HermiteRelative_symmetricOn_of_polySym
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
theorem solution (i : Fin d) : SymmetricOn (polyGaussCore (d := d)) (momL i) := symmetricOn_of_polySym (polySym_momPoly i)
