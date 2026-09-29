-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_X
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:02:49.673338+00:00
-- url     : https://prove2.me/submissions/1e8ae761-872f-471c-8fd1-adfa22c8d110

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_X
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin d) : starP (X j : MvPolynomial (Fin d) ℂ) = X j := by

  simp [starP]
