-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.pgFunT_apply_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:25:03.536135+00:00
-- url     : https://prove2.me/submissions/602c3096-46c1-4499-8421-836205fa2bc2

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.pgFunT_apply_add
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
theorem solution (a k : Vd d) (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (p + q) x = pgFunT a k p x + pgFunT a k q x := congrFun (pgFunT_add a k p q) x
