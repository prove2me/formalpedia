-- Prove2me | solution 1 for FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ee2032d3-f4e7-5c3f-8097-7dfac7b5d355

import Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_of_torsion
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem solution {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k] (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (hF : (Fintype.card F).Prime) (m : ℕ) (hm : 1 ≤ m) (hmk : (m : k) ≠ 0) : 0 < kerDeg (frobEnd W σ) m 1 ∧ ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) * m + Fintype.card F := by
  refine FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_of_torsion W σ hσ hF ?_
    (fun n => WeierstrassCurve.isCoprime_Phi_PsiSq (W⁄k) n) m hm hmk
  intro n x y h h0
  rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W⁄k) h.1 n,
    (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (W⁄k) h n).mp h0, zero_pow two_ne_zero]

end S_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq
end P2MW
export P2MW.S_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq (solution)
