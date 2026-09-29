-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.formallyUnramified_of_forall_representsOn_hom_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/40b19e76-046e-589d-8a25-632babaa242c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogenyPairRep
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_formallyUnramified_of_represents_isIsogenyPair_preservesLevel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_formallyUnramified_of_forall_representsOn_hom_isPullback
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace StrataUnram

theorem of_isPullback_charts (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {Xd M : Scheme.{0}} (q : Xd ⟶ M) (𝒰 : M.OpenCover)
    (h : ∀ i, ∃ (X : Scheme.{0}) (ξ : X ⟶ 𝒰.X i) (κ : X ⟶ Xd), IsPullback κ ξ q (𝒰.f i) ∧ P ξ) : P q := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) 𝒰
  intro i
  obtain ⟨X, ξ, κ, hsq, hP⟩ := h i
  have e : ξ = hsq.isoPullback.hom ≫ 𝒰.pullbackHom q i := by
    rw [Scheme.Cover.pullbackHom, IsPullback.isoPullback_hom_snd]
  rw [e] at hP
  exact (MorphismProperty.cancel_left_of_respectsIso P hsq.isoPullback.hom (𝒰.pullbackHom q i)).mp hP

end StrataUnram

open StrataUnram in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (r d : ℕ)

    (𝒪 : Type) [CommRing 𝒪] (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [Algebra 𝒪 C] (𝔄 : FakeEllipticCurve Λ N C)
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (hloc : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (Xd : Scheme.{0}) (q : Xd ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (κ : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xd))
    (hB1 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ S u A gA hgA X ξ pt hX ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap C S))))
    (hB2 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xd) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) →
            ∃! y : T ⟶ X, y ≫ κ S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t)) :
    FormallyUnramified q := by
  classical

  have chart : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (κ' : X ⟶ Xd), IsPullback κ' ξ q s ∧ FormallyUnramified ξ := by
    intro S _ s

    let φ : CommRingCat.of C ⟶ CommRingCat.of S :=
      Spec.preimage (s ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    letI : Algebra C S := RingHom.toAlgebra φ.hom
    letI : Algebra 𝒪 S := RingHom.toAlgebra (φ.hom.comp (algebraMap 𝒪 C))
    haveI : IsScalarTower 𝒪 C S := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    have hCS : Spec.map (CommRingCat.ofHom (algebraMap C S)) =
        s ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) := by
      show Spec.map (CommRingCat.ofHom φ.hom) = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hOS : Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S)) =
        s ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) ≫ fM := by
      show Spec.map (CommRingCat.ofHom ((algebraMap C S).comp (algebraMap 𝒪 C))) = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hCS, Category.assoc, Limits.pullback.condition]

    obtain ⟨u, hu⟩ := hM.ptF_surjective S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S)))
      ⟨s ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))), by rw [Category.assoc, hOS]⟩
    have hu1 : (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 =
        s ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) := congrArg Subtype.val hu

    obtain ⟨A, gA, hgAsq, hgAmul, hgAact, hgAlev, -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap C S) 𝔄
    have hgA : FakeEllipticCurve.IsPullbackVia (algebraMap C S) 𝔄 A gA := ⟨hgAsq, hgAmul, hgAact, hgAlev⟩
    obtain ⟨X, ξ, hlfp, pt, hX⟩ := hloc S u A gA hgA
    haveI := hlfp
    have hunr : FormallyUnramified ξ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.formallyUnramified_of_represents_isIsogenyPair_preservesLevel
        hΛℤ r d S u.1 A X ξ pt hX.1 hX.2.1 hX.2.2.1 hX.2.2.2

    have hcomm : κ S u A gA hgA X ξ pt hX ≫ q = ξ ≫ s := by
      obtain ⟨h1, h2⟩ := hB1 S u A gA hgA X ξ pt hX
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, h1, hu1, Category.assoc]
      · rw [Category.assoc, h2, hCS, Category.assoc]
    refine ⟨X, ξ, κ S u A gA hgA X ξ pt hX, ?_, hunr⟩
    refine IsPullback.of_isLimit' ⟨hcomm⟩ ?_

    have hcone : ∀ c : PullbackCone q s,
        c.fst ≫ q ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
            c.snd ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          c.fst ≫ q ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
            c.snd ≫ Spec.map (CommRingCat.ofHom (algebraMap C S)) := by
      intro c
      constructor
      · rw [← Category.assoc, c.condition, Category.assoc, hu1]
      · rw [← Category.assoc, c.condition, Category.assoc, hCS]
    have hlift := fun c : PullbackCone q s =>
      hB2 S u A gA hgA X ξ pt hX c.pt c.fst c.snd (hcone c).1 (hcone c).2
    exact PullbackCone.IsLimit.mk hcomm (fun c => (hlift c).exists.choose)
      (fun c => (hlift c).exists.choose_spec.1) (fun c => (hlift c).exists.choose_spec.2)
      (fun c m h1 h2 => (hlift c).unique ⟨h1, h2⟩ (hlift c).exists.choose_spec)

  apply of_isPullback_charts @FormallyUnramified q
    (Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))).affineCover
  intro i
  exact chart _ _

end S_CerednikDrinfeld_QM_IsFineModuli_formallyUnramified_of_forall_representsOn_hom_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_formallyUnramified_of_forall_representsOn_hom_isPullback (solution)
