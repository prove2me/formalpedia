-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_C
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:01:20.057716+00:00
-- url     : https://prove2.me/submissions/14ff8e37-f4b0-4966-95ae-8c142b629d99

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_C
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) : starP (C c : MvPolynomial (Fin d) ℂ) = C ((starRingEnd ℂ) c) := by

  simp [starP]
