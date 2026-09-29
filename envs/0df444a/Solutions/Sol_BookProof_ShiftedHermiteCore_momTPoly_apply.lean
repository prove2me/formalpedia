-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.momTPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:34.044556+00:00
-- url     : https://prove2.me/submissions/a55da610-98c4-41ed-90c3-9fbe0c6bdebb

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.momTPoly_apply
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momTPoly k i p = momPoly i p + ((k i : ℝ) : ℂ) • p := rfl
