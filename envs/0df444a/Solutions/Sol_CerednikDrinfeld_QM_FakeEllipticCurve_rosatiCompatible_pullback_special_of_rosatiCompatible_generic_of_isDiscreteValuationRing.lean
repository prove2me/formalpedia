-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_pullback_special_of_rosatiCompatible_generic_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ff997d9f-cefe-5cbd-a372-daa4f39982ec

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_rosatiCompatible_of_rosatiCompatible_generic_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_pullback_special_of_rosatiCompatible_generic_of_isDiscreteValuationRing
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (star : ↥Λ → ↥Λ)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    (k : Type) [Field k] (φ : R →+* k) (hφ : Function.Surjective φ)
    (E_R : FakeEllipticCurve Λ N R) (E_K : FakeEllipticCurve Λ N KK) (E : FakeEllipticCurve Λ N k)
    (gK : E_K.A ⟶ E_R.A) (hgK : CategoryTheory.IsPullback gK E_K.f E_R.f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
    (hgK_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of KK)) (P Q : SchemeHomOver t' E_K.f),
      (E_K.L.mul t' P Q).1 ≫ gK =
        (E_R.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R KK)))
          ⟨P.1 ≫ gK, by rw [Category.assoc, hgK.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gK, by rw [Category.assoc, hgK.w, ← Category.assoc, Q.2]⟩).1)
    (hgK_act : ∀ x : ↥Λ, E_K.act x ≫ gK = gK ≫ E_R.act x)
    (gk : E.A ⟶ E_R.A) (hgk : CategoryTheory.IsPullback gk E.f E_R.f (Spec.map (CommRingCat.ofHom φ)))
    (hgk_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gk =
        (E_R.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ gk, by rw [Category.assoc, hgk.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gk, by rw [Category.assoc, hgk.w, ← Category.assoc, Q.2]⟩).1)
    (hgk_act : ∀ x : ↥Λ, E.act x ≫ gk = gk ≫ E_R.act x)
    (𝓛 : E_R.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝓛K : E_K.A.Modules) (hiso : Nonempty ((Scheme.Modules.pullback gK).obj 𝓛 ≅ 𝓛K))
    (hros : RosatiCompatible E_K.f E_K.L 𝓛K E_K.act E_K.act_over star) :
    RosatiCompatible E.f E.L ((Scheme.Modules.pullback gk).obj 𝓛) E.act E.act_over star := by
  have hR : RosatiCompatible E_R.f E_R.L 𝓛 E_R.act E_R.act_over star :=
    GoodReductionJacobian.RelativeGroupLaw.rosatiCompatible_of_rosatiCompatible_generic_of_isDiscreteValuationRing
      R KK E_R.f E_R.L E_R.comm E_R.bundle E_K.f E_K.L gK hgK hgK_mul E_R.act E_R.act_over E_K.act E_K.act_over
      hgK_act star 𝓛 h𝓛 𝓛K hiso hros
  exact AlgebraicGeometry.Polarisation.RosatiCompatible.pullback_of_isPullback R k φ E_R.f E_R.L E.f E.L gk hgk hgk_mul
    E_R.act E_R.act_over E.act E.act_over hgk_act star 𝓛 h𝓛 hR

end S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_pullback_special_of_rosatiCompatible_generic_of_isDiscreteValuationRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_pullback_special_of_rosatiCompatible_generic_of_isDiscreteValuationRing (solution)
