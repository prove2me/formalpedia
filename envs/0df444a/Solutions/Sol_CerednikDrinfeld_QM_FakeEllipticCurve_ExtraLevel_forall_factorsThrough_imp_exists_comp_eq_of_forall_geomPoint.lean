-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.forall_factorsThrough_imp_exists_comp_eq_of_forall_geomPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/19be7d82-81be-50e8-8067-de46ccaf1b2f

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_forall_factorsThrough_imp_exists_comp_eq_of_forall_geomPoint
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S']
    (φ : S →+* S') (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (g : E'.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t E'.f),
      (E'.L.mul t P Q).1 ≫ g =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : S)) (K : E.ExtraLevel ℓ) (K' : E'.ExtraLevel ℓ)
    (hKK' : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k) (Q : SchemeHomOver (geomPoint k sk') E'.f),
      FactorsThrough K'.levK Q → ∃ Q₀ : Spec (CommRingCat.of k) ⟶ K.K, Q₀ ≫ K.levK = Q.1 ≫ g)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f)
    (hP : FactorsThrough K'.levK P) :
    ∃ P₀ : T ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ g := by

  obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback φ E E' g hg hg_mul hg_act t'
  have hR : (σ P).1 = P.1 ≫ g := hσ1 P
  rw [← hR]

  refine ((CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit E ℓ hℓ K).2
    (t' ≫ Spec.map (CommRingCat.ofHom φ)) (σ P)).2 ⟨?_, ?_⟩
  ·
    rw [← hσnsmul, K'.levK_torsion t' P hP, hσone]
  ·
    intro k _ _ sk τ hτ
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (τ ≫ t')
    have hτ' : τ ≫ t' = geomPoint k ψ.hom := by
      rw [← hψ]; rfl
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨Q₀, hQ₀⟩ := hKK' k ψ.hom (schemeHomOverComp τ hτ' P) ⟨τ ≫ P₀, by rw [Category.assoc, hP₀, schemeHomOverComp_coe]⟩
    refine ⟨Q₀, ?_⟩
    rw [hQ₀, schemeHomOverComp_coe, schemeHomOverComp_coe, hR, Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_forall_factorsThrough_imp_exists_comp_eq_of_forall_geomPoint
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_forall_factorsThrough_imp_exists_comp_eq_of_forall_geomPoint (solution)
