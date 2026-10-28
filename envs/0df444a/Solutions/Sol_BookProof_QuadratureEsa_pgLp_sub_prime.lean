-- Prove2me | solution 1 for BookProof.QuadratureEsa.pgLp_sub_prime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:47:08.287422+00:00
-- url     : https://prove2.me/submissions/7f404d86-b633-4554-932c-4728b03512ec

-- Generated from ChapterQuadratureEsa.lean — theorem BookProof.QuadratureEsa.pgLp_sub'
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
open BookProof.QuadratureEsa



open MeasureTheory MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

variable {d : ℕ}
theorem solution (p q : MvPolynomial (Fin d) ℂ) : pgLp (p - q) = pgLp p - pgLp q := by
  exact BookProof.QuadratureEsa.pgLp_sub' p q
