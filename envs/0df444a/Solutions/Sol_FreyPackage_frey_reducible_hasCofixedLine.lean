-- Prove2me | solution 1 for FreyPackage.frey_reducible_hasCofixedLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0bc98e21-af98-552b-a77e-28f9779e0a32

import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_FreyPackage_freyCurve_discriminant
import Theorems.Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed
import Theorems.Thm_FreyPackage_frey_torsion_fixed_eq_zero
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_reducible_hasCofixedLine
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem solution (P : FreyPackage)
    (hred : ¬ GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) :
    HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by
  classical

  haveI hE : P.freyCurve.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, P.freyCurve_discriminant, isUnit_iff_ne_zero]
    have h : ((P.a : ℚ) * P.b * P.c) ≠ 0 := by exact_mod_cast P.habc0
    exact div_ne_zero (pow_ne_zero _ h) (by norm_num)

  have hp : ((P.p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast P.hp0
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed
    (K := AlgebraicClosure ℚ) P.freyCurve hp
  have hnt : Nontrivial
      (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) := by
    have h1 : 1 < Nat.card
        (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) := by
      rw [hcard]
      have := P.hp5
      nlinarith
    haveI : Finite (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) :=
      Nat.finite_of_card_ne_zero (by omega)
    exact Finite.one_lt_card_iff_nontrivial.mp h1

  unfold GaloisRepIsIrreducible at hred
  push Not at hred
  obtain ⟨N, hN, hbot, htop⟩ := hred hnt
  refine ⟨N, hN, hbot, htop, ?_⟩

  rcases P.frey_stable_submodule_fixed_or_cofixed N hN hbot htop with hfix | hcofix
  · exfalso
    obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hbot
    exact hx0 (P.frey_torsion_fixed_eq_zero x (fun σ => hfix σ x hxN))
  · exact hcofix

end S_FreyPackage_frey_reducible_hasCofixedLine
end P2MW
export P2MW.S_FreyPackage_frey_reducible_hasCofixedLine (solution)
