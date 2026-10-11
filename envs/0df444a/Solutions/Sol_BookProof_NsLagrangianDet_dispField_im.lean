-- Prove2me | solution 1 for BookProof.NsLagrangianDet.dispField_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:18.691978+00:00
-- url     : https://prove2.me/submissions/cf1a0dc3-14b5-42f6-8cc4-7750bf7cde79

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.dispField_im
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) (i : Fin 3) :
    (dispField kv y a i).im = 0 := by

  unfold dispField
  rw [Fintype.sum_prod_type, Complex.im_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Fintype.sum_bool]
  have hconj : ev y (scoef (k, false) i) * phase (wv kv (k, false)) a
      = (starRingEnd ℂ) (ev y (scoef (k, true) i) * phase (wv kv (k, true)) a) := by
    simp only [scoef, wv, ev, phase, map_add, map_mul, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, if_true, Bool.false_eq_true, if_false]
    rw [← Complex.exp_conj]
    simp [Complex.conj_ofReal, Finset.sum_neg_distrib]
  rw [hconj, Complex.add_im, Complex.conj_im]
  ring
