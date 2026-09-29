-- Prove2me | solution 1 for BookProof.YangMillsHermite.derOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:49:18.221763+00:00
-- url     : https://prove2.me/submissions/e78de9b3-c020-4af0-a653-97bd9f0365c9

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.derOp_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp j p = pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p) := rfl
