-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:11:21.688492+00:00
-- url     : https://prove2.me/submissions/9535b864-f4ad-4557-acbc-2bdf8af32104

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_sub
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p q : MvPolynomial (Fin d) ℂ) :
    starP (p - q) = starP p - starP q := map_sub _ _ _
