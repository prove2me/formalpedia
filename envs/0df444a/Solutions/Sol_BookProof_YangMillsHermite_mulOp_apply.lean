-- Prove2me | solution 1 for BookProof.YangMillsHermite.mulOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:59:47.452802+00:00
-- url     : https://prove2.me/submissions/c2ebe71f-914b-4e97-8e2e-8ff56bfd2ca0

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.mulOp_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := rfl
