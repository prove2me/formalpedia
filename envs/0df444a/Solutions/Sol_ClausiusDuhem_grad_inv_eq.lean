-- Prove2me | solution 1 for ClausiusDuhem.grad_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T05:54:12.954968+00:00
-- url     : https://prove2.me/submissions/35e35781-16c5-4267-a017-9b427ef8f777

import Definitions.Def_ClausiusDuhem_field_calculus
set_option autoImplicit false
open ClausiusDuhem

theorem solution (T : Space → ℝ) (x : Space)
    (hT : DifferentiableAt ℝ T x) (hTx : T x ≠ 0) :
    grad (fun y => (T y)⁻¹) x = -(1 / T x ^ 2) • grad T x := by
  have hd := (hasDerivAt_inv hTx).comp_hasFDerivAt x hT.hasFDerivAt
  have he : fderiv ℝ (fun y => (T y)⁻¹) x = -(T x ^ 2)⁻¹ • fderiv ℝ T x := hd.fderiv
  ext j
  simp only [grad, partialDeriv, he, smul_apply,
    Pi.smul_apply, smul_eq_mul, one_div, neg_mul]

#print axioms solution
