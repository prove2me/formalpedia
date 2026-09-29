-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.withExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/dab4e680-bfe4-56ba-9c99-f1dfdb258177

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_forall_factorsThrough_imp_exists_comp_eq_of_forall_geomPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_withExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp_coe GoodReductionJacobian"

namespace G2Body

theorem coe_nsmulPt_eq_of_coe_eq {S : Type} [CommRing S] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₀ t₁ : T ⟶ Spec (CommRingCat.of S)} (h : t₀ = t₁)
    (Y : SchemeHomOver t₀ f) (Y' : SchemeHomOver t₁ f) (hY : Y.1 = Y'.1) (j : ℕ) :
    (nsmulPt L t₀ j Y).1 = (nsmulPt L t₁ j Y').1 := by
  subst h
  obtain rfl : Y = Y' := Subtype.ext hY
  rfl

end G2Body

open G2Body in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (m ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (hℓ : IsUnit ((ℓ : ℕ) : S))
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
    (K : u.1.ExtraLevel ℓ) (K' : u'.1.ExtraLevel ℓ)
    (hK : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) u.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (u.1.act x) (u.1.act_over x)
              (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk)) = Q)
    (hK' : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (Q : SchemeHomOver (geomPoint k sk) u'.1.f),
        FactorsThrough K'.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (u'.1.act x) (u'.1.act_over x)
              (nsmulPt u'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk)) = Q) :
    FakeEllipticCurve.WithExtraLevel.IsPullback φ (⟨u.1, K⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨u'.1, K'⟩ := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := hu
  refine ⟨g, hg, hmul, hact, fun t' P => ⟨hlev t' P, fun hPK' => ?_⟩⟩
  refine CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.forall_factorsThrough_imp_exists_comp_eq_of_forall_geomPoint
    φ u.1 u'.1 g hg hmul hact ℓ hℓ K K' ?_ t' P hPK'

  intro k _ _ sk' Q hQ
  obtain ⟨x, hx, hxQ⟩ := (hK' k sk' Q).mp hQ

  obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback φ u.1 u'.1 g hg hmul hact (geomPoint k sk')

  have hbase : geomPoint k sk' ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk'.comp φ) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl

  have hR₀ : FactorsThrough K.levK
      (pushPt (u.1.act x) (u.1.act_over x)
        (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) :=
    (hK k (sk'.comp φ) _).mpr ⟨x, hx, rfl⟩
  obtain ⟨Q₀, hQ₀⟩ := hR₀
  refine ⟨Q₀, ?_⟩
  rw [hQ₀, ← hxQ, ← hσ1, hσact, hσnsmul]
  simp only [pushPt, mapPt_coe]
  congr 1
  refine coe_nsmulPt_eq_of_coe_eq u.1.L hbase.symm _ _ ?_ (m / ℓ)

  rw [hσ1]
  simp only [FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc, hP]
  rw [← Category.assoc, hbase]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_withExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_withExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff (solution)
