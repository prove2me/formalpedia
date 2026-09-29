-- Prove2me | solution 1 for BookProof.YangMillsHermite.commutator_coord_mom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:27:48.287626+00:00
-- url     : https://prove2.me/submissions/f4fd5825-7fd6-4d20-912e-f6a37b999537

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.commutator_coord_mom
import Mathlib
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_momOp_apply
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X j) (momOp j p) - momOp j (mulOp (X j) p) = Complex.I • p := by

  have hX : (pderiv j) (X j * p) = p + X j * pderiv j p := by
    rw [Derivation.leibniz]
    simp only [pderiv_X_self, smul_eq_mul, mul_one]
    ring
  simp only [mulOp_apply, momOp_apply, hX, neg_smul, smul_eq_C_mul]
  ring
