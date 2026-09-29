-- Prove2me | solution 1 for FreyPackage.routeAReversePinBadOnlySeam_of_eigenformResidualAttachment
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7364f436-e15a-5b8c-901f-2b49eeaff5cd

import Mathlib
import Definitions.Def_FreyPackage_RouteAReversePinSeam
import Definitions.Def_FreyPackage_EigenformResidualAttachment
import Theorems.Thm_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_routeAReversePinBadOnlySeam_of_eigenformResidualAttachment
p2m_attr_erase "instance" "FreyCurve.instIsEllipticRatFreyCurve FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

theorem solution (P : FreyPackage)
    (hatt : ∀ M : ℕ, 0 < M → P.EigenformResidualAttachmentAt M) :
    P.RouteAReversePinBadOnlySeam :=
  fun _N _f _W _𝔪 hwit ℓ hℓ hgoodInt hℓN hℓp _hbadW =>
    FreyPackage.canonicalModelCongruence_of_eigenformResidualAttachment P hatt hwit ℓ hℓ hgoodInt hℓN hℓp

end S_FreyPackage_routeAReversePinBadOnlySeam_of_eigenformResidualAttachment
end P2MW
export P2MW.S_FreyPackage_routeAReversePinBadOnlySeam_of_eigenformResidualAttachment (solution)
