-- Prove2me | solution 1 for BookProof.YangMillsHermite.momOp_polySym
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:41:37.351007+00:00
-- url     : https://prove2.me/submissions/df84ebd6-7c60-4fe2-9a9a-1de0eb13ae7c

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.momOp_polySym
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_momOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_gaussInt_sub
import Theorems.Thm_BookProof_YangMillsHermite_gaussInt_leibniz
import Theorems.Thm_BookProof_YangMillsHermite_starP_momOp
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin d) : PolySym (momOp (d := d) j) := by

  intro p q
  have hleib := gaussInt_leibniz j (starP p) q
  have e1 : (X j : MvPolynomial (Fin d) ℂ) * starP p * q = X j * (starP p * q) := by ring
  have e2 : starP p * (X j * q) = X j * (starP p * q) := by ring
  have hL : gaussInt (starP (momOp j p) * q)
      = Complex.I * (gaussInt (pderiv j (starP p) * q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [starP_momOp, smul_mul_assoc, gaussInt_smul, sub_mul, gaussInt_sub, smul_mul_assoc,
      gaussInt_smul, e1]
  have hR : gaussInt (starP p * momOp j q)
      = -Complex.I * (gaussInt (starP p * pderiv j q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [momOp_apply, mul_smul_comm, gaussInt_smul, mul_sub, gaussInt_sub, mul_smul_comm,
      gaussInt_smul, e2]
  rw [hL, hR]
  push_cast
  linear_combination Complex.I * hleib
