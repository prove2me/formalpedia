-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.pgFunT_apply_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:25:04.770987+00:00
-- url     : https://prove2.me/submissions/1a11a074-5466-4f06-94ab-f406efc78e7c

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.pgFunT_apply_smul
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
theorem solution (a k : Vd d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (c • p) x = c * pgFunT a k p x := congrFun (pgFunT_smul a k c p) x
