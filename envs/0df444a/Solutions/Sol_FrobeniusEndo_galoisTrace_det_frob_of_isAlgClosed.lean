-- Prove2me | solution 1 for FrobeniusEndo.galoisTrace_det_frob_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bf6a818a-9546-5588-af2d-40d58fcd658f

import Theorems.Thm_FrobeniusEndo_galoisTrace_frob_eq_of_line_of_charEqOnPoints
import Theorems.Thm_FrobeniusEndo_frobCharEqOnPoints_of_frobenius
import Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_line_one
import Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_ne_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_galoisTrace_det_frob_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem solution {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k]
    [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k]
    (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
    (hF : (Fintype.card F).Prime) (p : ℕ) [Fact p.Prime] (hpk : (p : k) ≠ 0) :
    galoisTrace F W p σ = (Fintype.card F : ZMod p) + 1 - (Nat.card (W⁄F).Point : ZMod p) ∧
      LinearMap.det (galoisRepModuleEnd F W p σ) = (Fintype.card F : ZMod p) := by
  have hfull : Nat.card (Submodule.torsionBy ℤ (W⁄k).Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) (W⁄k) hpk
  exact FrobeniusEndo.galoisTrace_frob_eq_of_line_of_charEqOnPoints W σ hσ p hfull hpk _
    (fun m hm hmk => FrobeniusEndo.kerDeg_frobEnd_line_one W σ hσ hF m hm hmk)
    (fun m hm hmk => FrobeniusEndo.kerDeg_frobEnd_line_one_ne_zero W σ hσ hF m hm hmk)
    (FrobeniusEndo.frobCharEqOnPoints_of_frobenius W σ hσ hF)

end S_FrobeniusEndo_galoisTrace_det_frob_of_isAlgClosed
end P2MW
export P2MW.S_FrobeniusEndo_galoisTrace_det_frob_of_isAlgClosed (solution)
