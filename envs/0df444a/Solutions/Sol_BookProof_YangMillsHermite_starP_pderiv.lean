-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:09:41.925196+00:00
-- url     : https://prove2.me/submissions/0c55cd07-2223-4054-98eb-e94b0248bf17

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_pderiv
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
    starP (pderiv j p) = pderiv j (starP p) := (MvPolynomial.pderiv_map).symm
