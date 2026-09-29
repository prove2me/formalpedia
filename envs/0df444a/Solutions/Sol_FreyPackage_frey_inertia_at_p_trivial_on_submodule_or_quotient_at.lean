-- Prove2me | solution 1 for FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient_at
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5a3dd8a8-54e9-5cbb-99a2-6331e93c3485

import Theorems.Thm_Submodule_stableLine_fixed_or_cofixed_of_absorbing
import Theorems.Thm_FreyPackage_frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line
import Theorems.Thm_FreyPackage_frey_inertia_at_p_filtration_of_not_dvd_abc
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_FreyPackage_freyCurve_discriminant
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "WeierstrassCurve~card WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

theorem solution (P : FreyPackage) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime P.p) : (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ N, σ • x = x) ∨ (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x - x ∈ N) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩

  haveI hE : P.freyCurve.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, P.freyCurve_discriminant, isUnit_iff_ne_zero]
    have h : ((P.a : ℚ) * P.b * P.c) ≠ 0 := by exact_mod_cast P.habc0
    exact div_ne_zero (pow_ne_zero _ h) (by norm_num)
  have hp : ((P.p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast P.hp0
  have hcard : Nat.card (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) = P.p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ) P.freyCurve hp

  obtain ⟨M, hM, habs⟩ :
      ∃ M : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p),
        M ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          ∀ y : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • y - y ∈ M := by
    by_cases hdvd : (P.p : ℤ) ∣ P.a * P.b * P.c
    · exact P.frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line hdvd A hA N hN hbot htop
    · exact P.frey_inertia_at_p_filtration_of_not_dvd_abc hdvd A hA N hN hbot htop

  have := Submodule.stableLine_fixed_or_cofixed_of_absorbing hcard
    (S := (A.inertiaSubgroupIn ℚ : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    N (fun g _ x hx => hN g x hx) hbot htop M hM (fun g hg y => habs g hg y)
  rcases this with h | h
  · exact Or.inl fun σ hσ x hx => h σ hσ x hx
  · exact Or.inr fun σ hσ x => h σ hσ x

end S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at
end P2MW
export P2MW.S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at (solution)
