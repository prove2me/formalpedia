-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/87cbe9b4-3351-594d-999f-e8b738675b91

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_locIsoOnBase
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_of_pullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pos_pullback_of_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace Ws23CP

theorem inv_coe_congr {S : Type u} [CommRing S] {A Z : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {b₁ b₂ : Z ⟶ Spec (CommRingCat.of S)} (hb : b₁ = b₂)
    (P : SchemeHomOver b₁ f) (P' : SchemeHomOver b₂ f) (hP : P.1 = P'.1) :
    (L.inv b₁ P).1 = (L.inv b₂ P').1 := by
  subst hb
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'
  simp only at hP
  subst hP
  rfl

theorem negMor_comp_eq_comp_negMor {S S' : Type u} [CommRing S] [CommRing S']
    (ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} (g : A' ⟶ A)
    (hw : g ≫ f = f' ≫ ι) (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ ι) ⟨P.1 ≫ g, by rw [Category.assoc, hw, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hw, ← Category.assoc, Q.2]⟩).1) :
    negMor f' L' ≫ g = g ≫ negMor f L := by
  letI G' : Group (SchemeHomOver f' f') := L'.pointGroup f'
  letI G₁ : Group (SchemeHomOver (f' ≫ ι) f) := L.pointGroup (f' ≫ ι)
  letI G₂ : Group (SchemeHomOver f f) := L.pointGroup f
  letI G₃ : Group (SchemeHomOver (g ≫ f) f) := L.pointGroup (g ≫ f)

  let φ : SchemeHomOver f' f' →* SchemeHomOver (f' ≫ ι) f :=
    MonoidHom.mk' (fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hw, ← Category.assoc, P.2]⟩)
      (fun P Q => Subtype.ext (hmul f' P Q))
  have h1 : negMor f' L' ≫ g = (L.inv (f' ≫ ι) ⟨𝟙 A' ≫ g, by rw [Category.id_comp, hw]⟩).1 := by
    have := map_inv φ (idPt f')
    exact congrArg Subtype.val this

  let ψ : SchemeHomOver f f →* SchemeHomOver (g ≫ f) f :=
    MonoidHom.mk' (fun P => GoodReductionJacobian.schemeHomOverComp g rfl P)
      (fun P Q => L.mul_natural f (g ≫ f) g rfl P Q)
  have h2 : g ≫ negMor f L = (L.inv (g ≫ f) (GoodReductionJacobian.schemeHomOverComp g rfl (idPt f))).1 := by
    have := map_inv ψ (idPt f)
    exact congrArg Subtype.val this
  rw [h1, h2]
  exact inv_coe_congr L hw.symm _ _ (by simp [GoodReductionJacobian.schemeHomOverComp_coe, idPt])

theorem locIsoOnBase_of_iso {S' : Type u} [CommRing S'] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase p M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

end Ws23CP

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (hH0 : ∀ (T : Type) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd E.f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback E.f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (S' : Type) [CommRing S'] [Algebra S S'] (hff : Module.FaithfullyFlat S S')
    (L' : RelativeGroupLaw S' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    (hL' : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝓛' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules)
    (h𝓛' : CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L'
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓛')
    (hli : LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
        ((Scheme.Modules.pullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛) 𝓛') :
    E.IsCanonicalPol star 𝓛 := by
  haveI : Module.FaithfullyFlat S S' := hff
  haveI : IsProper E.f := E.bundle.proper
  have hg : IsPullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
      (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) E.f
      (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := IsPullback.of_hasPullback _ _

  have hP := CerednikDrinfeld.QM.IsCanonicalPolData.of_locIsoOnBase _ L' _ _ star 𝓛' _
    (h𝓛.pullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    ((LocIsoOnBase.equivalence _).symm hli) h𝓛'
  have hmul : ∀ {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
      (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1 :=
    fun t' P Q => hL' _ t' P Q
  refine ⟨h𝓛, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hneg := Ws23CP.negMor_comp_eq_comp_negMor (Spec.map (CommRingCat.ofHom (algebraMap S S')))
      (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) hg.w E.L L' hmul
    have e1 : (Scheme.Modules.pullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj
          ((Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓛) ≅
        (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj
          ((Scheme.Modules.pullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛) :=
      (Scheme.Modules.pullbackComp (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (negMor E.f E.L)).app 𝓛 ≪≫
        (Scheme.Modules.pullbackCongr hneg.symm).app 𝓛 ≪≫
        ((Scheme.Modules.pullbackComp (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')
          (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).app 𝓛).symm
    have hiso := (LocIsoOnBase.equivalence (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).trans
      (Ws23CP.locIsoOnBase_of_iso _ e1) hP.2.1
    exact LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated S' E.f
      (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
      hg hH0 _ 𝓛 (h𝓛.pullback _) h𝓛 hiso
  ·
    exact KernelIsTwoTorsion.of_pullback_of_faithfullyFlat hg E.L E.bundle L' hmul 𝓛 h𝓛 hP.2.2.1
  ·
    exact AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat
      E.f E.L S' hff L' hL' 𝓛 h𝓛 hP.2.2.2.1
  ·
    intro k _ _ sk
    exact AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_pos_pullback_of_faithfullyFlat E.f
      (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
      hg 𝓛 h𝓛 hP.2.2.2.2.1 k sk
  ·
    exact RosatiCompatible.of_pullback_of_faithfullyFlat E.f E.L E.bundle
      (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L'
      (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) hg hmul E.act E.act_over _ _
      (fun b => pullback.lift_fst _ _ _) star 𝓛 h𝓛 hP.2.2.2.2.2

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat (solution)
