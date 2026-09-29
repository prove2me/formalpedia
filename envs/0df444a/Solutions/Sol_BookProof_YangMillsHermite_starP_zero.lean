-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:14:30.786094+00:00
-- url     : https://prove2.me/submissions/e528c6dc-48fc-4214-a3e2-c56d26aa9549

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_zero
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution : starP (0 : MvPolynomial (Fin d) ℂ) = 0 := map_zero _
