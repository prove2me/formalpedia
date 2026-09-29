-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_momOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:38:12.720196+00:00
-- url     : https://prove2.me/submissions/c4456e28-e7ff-45a7-b0bb-eaeaf6d00275

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_momOp
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_starP_mul
import Theorems.Thm_BookProof_YangMillsHermite_starP_X
import Theorems.Thm_BookProof_YangMillsHermite_starP_smul
import Theorems.Thm_BookProof_YangMillsHermite_starP_real_smul
import Theorems.Thm_BookProof_YangMillsHermite_momOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_starP_pderiv
import Theorems.Thm_BookProof_YangMillsHermite_starP_neg
import Theorems.Thm_BookProof_YangMillsHermite_starP_sub
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (momOp j p)
      = Complex.I • (pderiv j (starP p) - ((1 / 2 : ℝ) : ℂ) • (X j * starP p)) := by

  rw [momOp_apply, neg_smul, starP_neg, starP_smul, starP_sub, starP_pderiv, starP_real_smul,
    starP_mul, starP_X, Complex.conj_I, neg_smul, neg_neg]
