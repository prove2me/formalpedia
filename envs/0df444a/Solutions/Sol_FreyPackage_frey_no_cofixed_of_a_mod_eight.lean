-- Prove2me | solution 1 for FreyPackage.frey_no_cofixed_of_a_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ebdbbe5d-fb00-5ee4-a492-709f16bf9f13

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_Submodule_not_exists_cofixed_line_of_inertia_and_branch_swap
import Theorems.Thm_FreyPackage_frey_exists_inertia_not_fixed_at_two
import Theorems.Thm_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight
import Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
import Theorems.Thm_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_FreyPackage_freyCurveInt_map
import Theorems.Thm_FreyPackage_freyCurveInt_discr_ne_zero
import Theorems.Thm_FreyPackage_dvd_freyCurveInt_discr_iff
import Theorems.Thm_FreyPackage_not_dvd_freyCurveInt_c4
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_no_cofixed_of_a_mod_eight
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (P : FreyPackage)
    (h8 : (P.a : ZMod 8) = 3) :
    ¬ HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by

  rw [← FreyPackage.freyCurveInt_map P]

  obtain ⟨A, hA, -⟩ := ValuationSubring.exists_isFrobeniusAt_rat 2 Nat.prime_two

  have h2b : (2 : ℤ) ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).mp P.hb2
  have h2abc : ((2 : ℕ) : ℤ) ∣ P.a * P.b * P.c := by
    exact_mod_cast (h2b.mul_left P.a).mul_right P.c
  have hΔ : P.freyCurveInt.Δ ≠ 0 := FreyPackage.freyCurveInt_discr_ne_zero P
  have h2Δ : ((2 : ℕ) : ℤ) ∣ P.freyCurveInt.Δ :=
    (FreyPackage.dvd_freyCurveInt_discr_iff P Nat.prime_two).mpr h2abc
  have h2c₄ : ¬ ((2 : ℕ) : ℤ) ∣ P.freyCurveInt.c₄ :=
    FreyPackage.not_dvd_freyCurveInt_c4 P Nat.prime_two h2abc

  obtain ⟨M, hMiff, -, -⟩ :=
    WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
      P.freyCurveInt Nat.prime_two hΔ h2Δ h2c₄ A hA P.pp

  haveI hEll : (P.freyCurveInt.map (Int.castRingHom ℚ)).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
    simp only [Int.coe_castRingHom]
    exact isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hΔ)

  have hcard : Nat.card (Submodule.torsionBy ℤ
      ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p) = P.p ^ 2 := by
    refine WeierstrassCurve.card_torsion_of_isAlgClosed
      (P.freyCurveInt.map (Int.castRingHom ℚ)) ?_
    exact_mod_cast (Nat.cast_ne_zero (R := AlgebraicClosure ℚ)).mpr P.pp.pos.ne'

  have hMtop : M ≠ ⊤ := by
    obtain ⟨x, hx⟩ :=
      WeierstrassCurve.exists_torsion_not_inZeroComponentAt_of_multiplicativeReduction
        P.freyCurveInt Nat.prime_two hΔ h2Δ h2c₄ A hA P.pp
    intro hM
    exact hx ((hMiff x).mp (hM ▸ Submodule.mem_top))

  have hIquo : ∀ τ ∈ (A.inertiaSubgroupIn ℚ : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))),
      ∀ y : Submodule.torsionBy ℤ
        ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
      τ • y - y ∈ M := by
    intro τ hτ y
    have := WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
      P.freyCurveInt Nat.prime_two hΔ h2Δ h2c₄ A hA τ hτ
      (y : ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    exact (hMiff (τ • y - y)).mpr this

  have hIram :
      ∃ τ ∈ (A.inertiaSubgroupIn ℚ : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))),
        ∃ y : Submodule.torsionBy ℤ
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
          τ • y ≠ y :=
    FreyPackage.frey_exists_inertia_not_fixed_at_two P A hA

  have hswap : ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      ∀ y : Submodule.torsionBy ℤ
        ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
      y ∉ M → σ • y + y ∈ M := by
    obtain ⟨σ, -, hσ⟩ :=
      FreyPackage.frey_exists_decomposition_branch_swap_of_a_mod_eight P h8 A hA
    exact ⟨σ, fun y hy => (hMiff (σ • y + y)).mpr (hσ y ((hMiff y).not.mp hy))⟩

  exact Submodule.not_exists_cofixed_line_of_inertia_and_branch_swap
    P.pp (by have := P.hp5; omega) hcard hMtop hIquo hIram hswap

end S_FreyPackage_frey_no_cofixed_of_a_mod_eight
end P2MW
export P2MW.S_FreyPackage_frey_no_cofixed_of_a_mod_eight (solution)
