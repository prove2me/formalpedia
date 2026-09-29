-- Prove2me | solution 1 for FreyPackage.frey_stable_submodule_fixed_or_cofixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/baaba1f3-ae8d-5e6b-9d8e-757576791968

import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_FreyPackage_freyCurve_discriminant
import Theorems.Thm_FreyPackage_freyGaloisRep_isUnramifiedAt
import Theorems.Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule
import Theorems.Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient
import Theorems.Thm_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial
import Theorems.Thm_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_stable_submodule_fixed_or_cofixed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (P : FreyPackage) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p))
    (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x ∈ N, σ • x = x) ∨
    (∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x - x ∈ N) := by
  classical

  haveI hE : P.freyCurve.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, P.freyCurve_discriminant, isUnit_iff_ne_zero]
    have h : ((P.a : ℚ) * P.b * P.c) ≠ 0 := by exact_mod_cast P.habc0
    exact div_ne_zero (pow_ne_zero _ h) (by norm_num)
  have hp : ((P.p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast P.hp0
  haveI : Finite (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) :=
    Nat.finite_of_card_ne_zero (by
      rw [WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ) P.freyCurve hp]
      exact pow_ne_zero _ P.hp0)
  rcases P.frey_inertia_at_p_trivial_on_submodule_or_quotient N hN hbot htop with hsub | hquot
  · left
    apply WeierstrassCurve.galois_action_trivial_on_submodule_of_inertia_trivial P.freyCurve N
    intro q hq A hA σ hσ x hxN
    by_cases hq2 : q = 2
    · subst hq2
      exact (P.frey_inertia_at_two_trivial_on_stable_submodule N hN hbot htop A hA σ hσ).1 x hxN
    by_cases hqp : q = P.p
    · subst hqp
      exact hsub A hA σ hσ x hxN
    · exact P.freyGaloisRep_isUnramifiedAt hq hq2 hqp A hA σ hσ x
  · right
    apply WeierstrassCurve.galois_action_trivial_on_quotient_of_inertia_trivial P.freyCurve N hN
    intro q hq A hA σ hσ x
    by_cases hq2 : q = 2
    · subst hq2
      exact (P.frey_inertia_at_two_trivial_on_stable_submodule N hN hbot htop A hA σ hσ).2 x
    by_cases hqp : q = P.p
    · subst hqp
      exact hquot A hA σ hσ x
    · have hfix : σ • x = x := P.freyGaloisRep_isUnramifiedAt hq hq2 hqp A hA σ hσ x
      rw [hfix, sub_self]
      exact N.zero_mem

end S_FreyPackage_frey_stable_submodule_fixed_or_cofixed
end P2MW
export P2MW.S_FreyPackage_frey_stable_submodule_fixed_or_cofixed (solution)
