-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.pgLpT_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:25:06.927598+00:00
-- url     : https://prove2.me/submissions/62c681c6-3fc8-4b4b-b137-0b8fbdaa659f

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.pgLpT_smul
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
theorem solution (a k : Vd d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    pgLpT a k (c • p) = c • pgLpT a k p := (pgMapT a k).map_smul c p
