-- Prove2me | solution 1 for BookProof.HermiteLadder.hamPolyL_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T14:56:04.708144+00:00
-- url     : https://prove2.me/submissions/ea2d07a9-a9c6-441a-8007-3edeb5180f91

-- Generated from ChapterHermiteLadderOrder.lean — solution of BookProof.HermiteLadder.hamPolyL_apply
import Mathlib
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
open BookProof.HermiteLadder




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (S : Finset (Fin d)) (q p : MvPolynomial (Fin d) ℂ) :
    hamPolyL S q p = kinPolyS S p + q * p := rfl
