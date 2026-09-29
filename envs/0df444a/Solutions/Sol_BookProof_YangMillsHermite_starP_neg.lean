-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:08:01.318382+00:00
-- url     : https://prove2.me/submissions/d554cf01-d60f-459c-8f93-ba1d482c772b

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_neg
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : MvPolynomial (Fin d) ℂ) : starP (-p) = -starP p := map_neg _ _
