-- Prove2me | solution 1 for BookProof.YangMillsHermite.realCoeff_X
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:29:17.804632+00:00
-- url     : https://prove2.me/submissions/d868dad5-703c-4abe-aec4-d8df68943927

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.realCoeff_X
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_starP_X
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin d) : RealCoeff (X j : MvPolynomial (Fin d) ℂ) := starP_X j
