-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_represents_homPair_act_comp_eq_of_closedImmersionBySections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a6003e38-5002-5512-95b1-ec629b78f1ce

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver
import Theorems.Thm_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_of_closedImmersionBySections_lfp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_represents_homPair_act_comp_eq_of_closedImmersionBySections
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace PairEq

variable {R : Type} [CommRing R]

def IsHom {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R))
    (LA : RelativeGroupLaw R f) (LB : RelativeGroupLaw R g)
    {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) : Prop :=
  ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
    pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
      (LB.mul (t' ≫ s)
        ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
        ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1

noncomputable def BC {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R))
    {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') (φ : pullback f s ⟶ B) : pullback f s'' ⟶ B :=
  pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
    (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ

theorem BC_over {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R))
    {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    BC f ψ s s'' hs φ ≫ g = pullback.snd f s'' ≫ s'' := by
  rw [BC, Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]

theorem specMap_comp {S' S'' : Type} [CommRing S'] [CommRing S''] (φ₀ : R →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ₀) = Spec.map (CommRingCat.ofHom (ψ.comp φ₀)) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

structure HomRep {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R))
    (LA : RelativeGroupLaw R f) (LB : RelativeGroupLaw R g) where
  H : Scheme.{0}
  πH : H ⟶ Spec (CommRingCat.of R)
  pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback f s ⟶ B), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πH
  nat : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1
  surj : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ∧
          pt S' s φ hφ = x
  inj : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ φ' : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ' =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ'

theorem isHom_baseChange {A B : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) :
    ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
      (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
      (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
      (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s)
      (φ'' : pullback f s'' ⟶ B) (hφ'' : φ'' ≫ g = pullback.snd f s'' ≫ s''),
      φ'' = pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
          (M.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') f),
        pullback.lift (L.mul (t' ≫ s'') P Q).1 t' (L.mul (t' ≫ s'') P Q).2 ≫ φ'' =
          (M.mul (t' ≫ s'')
            ⟨pullback.lift P.1 t' P.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩).1) := by
  intro S' S'' _ _ ψ s s'' hs φ hφ φ'' hφ'' hG H T t' P Q
  subst hG
  have e : (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ s = t' ≫ s'' := by rw [Category.assoc, hs]
  have liftG : ∀ (R' : T ⟶ A) (hR : R' ≫ f = t' ≫ s''),
      pullback.lift R' t' hR ≫ pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
          (by rw [Category.assoc, hs]; exact pullback.condition) =
        pullback.lift R' (t' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [e]; exact hR) := by
    intro R' hR
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  have genL : ∀ {u v : T ⟶ Spec (CommRingCat.of R)} (huv : v = u) (X Y : SchemeHomOver u f),
      (L.mul u X Y).1 = (L.mul v ⟨X.1, X.2.trans huv.symm⟩ ⟨Y.1, Y.2.trans huv.symm⟩).1 := by
    intro u v huv X Y
    subst huv
    rfl
  have genM : ∀ {u v : T ⟶ Spec (CommRingCat.of R)} (huv : v = u) (X Y : SchemeHomOver u g),
      (M.mul u X Y).1 = (M.mul v ⟨X.1, X.2.trans huv.symm⟩ ⟨Y.1, Y.2.trans huv.symm⟩).1 := by
    intro u v huv X Y
    subst huv
    rfl
  rw [← Category.assoc, liftG]
  have step : pullback.lift (L.mul (t' ≫ s'') P Q).1 (t' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [e]; exact (L.mul (t' ≫ s'') P Q).2) =
      pullback.lift (L.mul ((t' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ s) ⟨P.1, P.2.trans e.symm⟩ ⟨Q.1, Q.2.trans e.symm⟩).1
        (t' ≫ Spec.map (CommRingCat.ofHom ψ))
        (L.mul ((t' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ s) ⟨P.1, P.2.trans e.symm⟩ ⟨Q.1, Q.2.trans e.symm⟩).2 := by
    congr 1
    exact genL e P Q
  rw [step, H T (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨P.1, P.2.trans e.symm⟩ ⟨Q.1, Q.2.trans e.symm⟩, genM e]
  congr 2
  · apply Subtype.ext
    dsimp only
    rw [← Category.assoc (pullback.lift P.1 t' P.2), liftG]
  · apply Subtype.ext
    dsimp only
    rw [← Category.assoc (pullback.lift Q.1 t' Q.2), liftG]

theorem exists_op₂
    {A₁ B₁ A₂ B₂ A₃ B₃ : Scheme.{0}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {g₁ : B₁ ⟶ Spec (CommRingCat.of R)}
    {f₂ : A₂ ⟶ Spec (CommRingCat.of R)} {g₂ : B₂ ⟶ Spec (CommRingCat.of R)}
    {f₃ : A₃ ⟶ Spec (CommRingCat.of R)} {g₃ : B₃ ⟶ Spec (CommRingCat.of R)}
    {L₁ : RelativeGroupLaw R f₁} {M₁ : RelativeGroupLaw R g₁}
    {L₂ : RelativeGroupLaw R f₂} {M₂ : RelativeGroupLaw R g₂}
    {L₃ : RelativeGroupLaw R f₃} {M₃ : RelativeGroupLaw R g₃}
    (D₁ : HomRep f₁ g₁ L₁ M₁) (D₂ : HomRep f₂ g₂ L₂ M₂) (D₃ : HomRep f₃ g₃ L₃ M₃)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R)) (q₁ : X ⟶ D₁.H) (q₂ : X ⟶ D₂.H)
    (hq₁ : q₁ ≫ D₁.πH = πX) (hq₂ : q₂ ≫ D₂.πH = πX)
    (F : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s)
        (φ₂ : pullback f₂ s ⟶ B₂) (hφ₂ : φ₂ ≫ g₂ = pullback.snd f₂ s ≫ s), (pullback f₃ s ⟶ B₃))
    (hF : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s)
        (φ₂ : pullback f₂ s ⟶ B₂) (hφ₂ : φ₂ ≫ g₂ = pullback.snd f₂ s ≫ s),
        F S' s φ₁ hφ₁ φ₂ hφ₂ ≫ g₃ = pullback.snd f₃ s ≫ s)
    (hFnat : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
        (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
        (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
        (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s)
        (φ₂ : pullback f₂ s ⟶ B₂) (hφ₂ : φ₂ ≫ g₂ = pullback.snd f₂ s ≫ s),
        F S'' s'' (BC f₁ ψ s s'' hs φ₁) (BC_over f₁ g₁ ψ s s'' hs φ₁ hφ₁) (BC f₂ ψ s s'' hs φ₂) (BC_over f₂ g₂ ψ s s'' hs φ₂ hφ₂) =
          BC f₃ ψ s s'' hs (F S' s φ₁ hφ₁ φ₂ hφ₂)) :
    ∃ op : X ⟶ D₃.H, op ≫ D₃.πH = πX ∧
      ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s)
        (φ₂ : pullback f₂ s ⟶ B₂) (hφ₂ : φ₂ ≫ g₂ = pullback.snd f₂ s ≫ s),
        IsHom f₁ g₁ L₁ M₁ s φ₁ hφ₁ → IsHom f₂ g₂ L₂ M₂ s φ₂ hφ₂ →
        ∀ z : SchemeHomOver s πX, z.1 ≫ q₁ = (D₁.pt S' s φ₁ hφ₁).1 → z.1 ≫ q₂ = (D₂.pt S' s φ₂ hφ₂).1 →
          z.1 ≫ op = (D₃.pt S' s (F S' s φ₁ hφ₁ φ₂ hφ₂) (hF S' s φ₁ hφ₁ φ₂ hφ₂)).1 := by
  classical

  have Fcongr : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (φ₁ φ₁' : pullback f₁ s ⟶ B₁) (h₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s) (h₁' : φ₁' ≫ g₁ = pullback.snd f₁ s ≫ s)
      (φ₂ φ₂' : pullback f₂ s ⟶ B₂) (h₂ : φ₂ ≫ g₂ = pullback.snd f₂ s ≫ s) (h₂' : φ₂' ≫ g₂ = pullback.snd f₂ s ≫ s),
      φ₁ = φ₁' → φ₂ = φ₂' → F S' s φ₁ h₁ φ₂ h₂ = F S' s φ₁' h₁' φ₂' h₂' := by
    intro S' _ s φ₁ φ₁' h₁ h₁' φ₂ φ₂' h₂ h₂' e₁ e₂; subst e₁; subst e₂; rfl
  have ptcongr : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (χ χ' : pullback f₃ s ⟶ B₃) (h : χ ≫ g₃ = pullback.snd f₃ s ≫ s) (h' : χ' ≫ g₃ = pullback.snd f₃ s ≫ s),
      χ = χ' → (D₃.pt S' s χ h).1 = (D₃.pt S' s χ' h').1 := by
    intro S' _ s χ χ' h h' e; subst e; rfl

  have hco₁ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), (x.1 ≫ q₁) ≫ D₁.πH = s := by
    intro S' _ s x; rw [Category.assoc, hq₁]; exact x.2
  have hco₂ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), (x.1 ≫ q₂) ≫ D₂.πH = s := by
    intro S' _ s x; rw [Category.assoc, hq₂]; exact x.2

  let Φ₁ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), (pullback f₁ s ⟶ B₁) :=
    fun S' _ s x => (D₁.surj S' s ⟨x.1 ≫ q₁, hco₁ S' s x⟩).choose
  have hΦ₁ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), Φ₁ S' s x ≫ g₁ = pullback.snd f₁ s ≫ s :=
    fun S' _ s x => (D₁.surj S' s ⟨x.1 ≫ q₁, hco₁ S' s x⟩).choose_spec.choose
  have homΦ₁ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), IsHom f₁ g₁ L₁ M₁ s (Φ₁ S' s x) (hΦ₁ S' s x) :=
    fun S' _ s x => (D₁.surj S' s ⟨x.1 ≫ q₁, hco₁ S' s x⟩).choose_spec.choose_spec.1
  have ptΦ₁ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), D₁.pt S' s (Φ₁ S' s x) (hΦ₁ S' s x) = ⟨x.1 ≫ q₁, hco₁ S' s x⟩ :=
    fun S' _ s x => (D₁.surj S' s ⟨x.1 ≫ q₁, hco₁ S' s x⟩).choose_spec.choose_spec.2
  let Φ₂ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), (pullback f₂ s ⟶ B₂) :=
    fun S' _ s x => (D₂.surj S' s ⟨x.1 ≫ q₂, hco₂ S' s x⟩).choose
  have hΦ₂ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), Φ₂ S' s x ≫ g₂ = pullback.snd f₂ s ≫ s :=
    fun S' _ s x => (D₂.surj S' s ⟨x.1 ≫ q₂, hco₂ S' s x⟩).choose_spec.choose
  have homΦ₂ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), IsHom f₂ g₂ L₂ M₂ s (Φ₂ S' s x) (hΦ₂ S' s x) :=
    fun S' _ s x => (D₂.surj S' s ⟨x.1 ≫ q₂, hco₂ S' s x⟩).choose_spec.choose_spec.1
  have ptΦ₂ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver s πX), D₂.pt S' s (Φ₂ S' s x) (hΦ₂ S' s x) = ⟨x.1 ≫ q₂, hco₂ S' s x⟩ :=
    fun S' _ s x => (D₂.surj S' s ⟨x.1 ≫ q₂, hco₂ S' s x⟩).choose_spec.choose_spec.2

  let e : ∀ (T : Type) [CommRing T] (φ₀ : R →+* T),
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ₀)) πX → SchemeHomOver (Spec.map (CommRingCat.ofHom φ₀)) D₃.πH :=
    fun T _ φ₀ x => D₃.pt T (Spec.map (CommRingCat.ofHom φ₀))
      (F T _ (Φ₁ T _ x) (hΦ₁ T _ x) (Φ₂ T _ x) (hΦ₂ T _ x)) (hF T _ (Φ₁ T _ x) (hΦ₁ T _ x) (Φ₂ T _ x) (hΦ₂ T _ x))

  have he : ∀ (T T' : Type) [CommRing T] [CommRing T'] (φ₀ : R →+* T) (ψ : T →+* T')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ₀)) πX),
      (e T' (ψ.comp φ₀) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
          rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
        Spec.map (CommRingCat.ofHom ψ) ≫ (e T φ₀ x).1 := by
    intro T T' _ _ φ₀ ψ x

    have hs : Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map (CommRingCat.ofHom φ₀)) = (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) :=
      specMap_comp φ₀ ψ
    have hx' : (Spec.map (CommRingCat.ofHom ψ) ≫ x.1) ≫ πX = (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) := by
      rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

    have step1₁ : Φ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩ = BC f₁ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) := by
      refine D₁.inj T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) _ _ (hΦ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (BC_over f₁ g₁ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x))
        (homΦ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩)
        (isHom_baseChange L₁ M₁ T T' ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) _ (BC_over f₁ g₁ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x)) rfl
          (homΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x)) ?_
      apply Subtype.ext
      rw [ptΦ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩]
      have hn : (D₁.pt T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) (BC f₁ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x)) (BC_over f₁ g₁ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x))).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (D₁.pt T (Spec.map (CommRingCat.ofHom φ₀)) (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x)).1 :=
        D₁.nat T T' ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x)
      rw [hn, ptΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x]
      simp only [Category.assoc]
    have step1₂ : Φ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩ = BC f₂ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) := by
      refine D₂.inj T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) _ _ (hΦ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (BC_over f₂ g₂ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x))
        (homΦ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩)
        (isHom_baseChange L₂ M₂ T T' ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) _ (BC_over f₂ g₂ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)) rfl
          (homΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)) ?_
      apply Subtype.ext
      rw [ptΦ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩]
      have hn : (D₂.pt T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) (BC f₂ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)) (BC_over f₂ g₂ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x))).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (D₂.pt T (Spec.map (CommRingCat.ofHom φ₀)) (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)).1 :=
        D₂.nat T T' ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)
      rw [hn, ptΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x]
      simp only [Category.assoc]

    have step2 : F T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) (Φ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (hΦ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩)
          (Φ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (hΦ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) =
        BC f₃ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (F T (Spec.map (CommRingCat.ofHom φ₀)) (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)) := by
      rw [Fcongr T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) _ _ (hΦ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (BC_over f₁ g₁ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x))
        _ _ (hΦ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (BC_over f₂ g₂ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)) step1₁ step1₂]
      exact hFnat T T' ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x)

    show (D₃.pt T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) _ (hF T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) (Φ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (hΦ₁ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩)
          (Φ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩) (hΦ₂ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, hx'⟩))).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (D₃.pt T (Spec.map (CommRingCat.ofHom φ₀)) _ (hF T (Spec.map (CommRingCat.ofHom φ₀)) (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x))).1
    rw [ptcongr T' (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) _ _ _ (BC_over f₃ g₃ ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hF T (Spec.map (CommRingCat.ofHom φ₀)) (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x))) step2]
    exact D₃.nat T T' ψ (Spec.map (CommRingCat.ofHom φ₀)) (Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) hs _ (hF T (Spec.map (CommRingCat.ofHom φ₀)) (Φ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₁ T (Spec.map (CommRingCat.ofHom φ₀)) x) (Φ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x) (hΦ₂ T (Spec.map (CommRingCat.ofHom φ₀)) x))
  obtain ⟨ε, hε, hεpt, -⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver πX D₃.πH e he
  refine ⟨ε, hε, ?_⟩
  intro S' _ s φ₁ hφ₁ φ₂ hφ₂ hom₁ hom₂ z hz₁ hz₂
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : R →+* S', Spec.map (CommRingCat.ofHom φ₀) = s :=
    ⟨(Spec.preimage s).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  subst hφ₀
  rw [hεpt S' φ₀ z]
  have hΦz₁ : Φ₁ S' _ z = φ₁ := by
    refine D₁.inj S' _ _ _ (hΦ₁ S' _ z) hφ₁ (homΦ₁ S' _ z) hom₁ ?_
    rw [ptΦ₁ S' _ z]
    exact Subtype.ext hz₁
  have hΦz₂ : Φ₂ S' _ z = φ₂ := by
    refine D₂.inj S' _ _ _ (hΦ₂ S' _ z) hφ₂ (homΦ₂ S' _ z) hom₂ ?_
    rw [ptΦ₂ S' _ z]
    exact Subtype.ext hz₂
  exact ptcongr S' _ _ _ _ _ (Fcongr S' _ _ _ (hΦ₁ S' _ z) hφ₁ _ _ (hΦ₂ S' _ z) hφ₂ hΦz₁ hΦz₂)

section Instances

variable {A₁ B₁ A₂ B₂ A₃ B₃ : Scheme.{0}}
  {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {g₁ : B₁ ⟶ Spec (CommRingCat.of R)}
  {f₂ : A₂ ⟶ Spec (CommRingCat.of R)} {g₂ : B₂ ⟶ Spec (CommRingCat.of R)}
  {f₃ : A₃ ⟶ Spec (CommRingCat.of R)} {g₃ : B₃ ⟶ Spec (CommRingCat.of R)}
  {L₁ : RelativeGroupLaw R f₁} {M₁ : RelativeGroupLaw R g₁}
  {L₂ : RelativeGroupLaw R f₂} {M₂ : RelativeGroupLaw R g₂}
  {L₃ : RelativeGroupLaw R f₃} {M₃ : RelativeGroupLaw R g₃}

theorem sem₁_of_sem₂ (D₁ : HomRep f₁ g₁ L₁ M₁) (D₂ : HomRep f₂ g₂ L₂ M₂) (D₃ : HomRep f₃ g₃ L₃ M₃)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R)) (q₁ : X ⟶ D₁.H) (q₂ : X ⟶ D₂.H)
    (hq₂ : q₂ ≫ D₂.πH = πX)
    (F₁ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s), (pullback f₃ s ⟶ B₃))
    (hF₁ : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s), F₁ S' s φ₁ hφ₁ ≫ g₃ = pullback.snd f₃ s ≫ s)
    (op : X ⟶ D₃.H)
    (hsem : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s)
        (φ₂ : pullback f₂ s ⟶ B₂) (hφ₂ : φ₂ ≫ g₂ = pullback.snd f₂ s ≫ s),
        IsHom f₁ g₁ L₁ M₁ s φ₁ hφ₁ → IsHom f₂ g₂ L₂ M₂ s φ₂ hφ₂ →
        ∀ z : SchemeHomOver s πX, z.1 ≫ q₁ = (D₁.pt S' s φ₁ hφ₁).1 → z.1 ≫ q₂ = (D₂.pt S' s φ₂ hφ₂).1 →
          z.1 ≫ op = (D₃.pt S' s (F₁ S' s φ₁ hφ₁) (hF₁ S' s φ₁ hφ₁)).1) :
    ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s), IsHom f₁ g₁ L₁ M₁ s φ₁ hφ₁ →
      ∀ z : SchemeHomOver s πX, z.1 ≫ q₁ = (D₁.pt S' s φ₁ hφ₁).1 →
        z.1 ≫ op = (D₃.pt S' s (F₁ S' s φ₁ hφ₁) (hF₁ S' s φ₁ hφ₁)).1 := by
  intro S' _ s φ₁ hφ₁ hom₁ z hz₁
  have hco₂ : (z.1 ≫ q₂) ≫ D₂.πH = s := by rw [Category.assoc, hq₂]; exact z.2
  obtain ⟨φ₂, hφ₂, hom₂, hpt₂⟩ := D₂.surj S' s ⟨z.1 ≫ q₂, hco₂⟩
  have hz₂ : z.1 ≫ q₂ = (D₂.pt S' s φ₂ hφ₂).1 := by rw [hpt₂]
  exact hsem S' s φ₁ hφ₁ φ₂ hφ₂ hom₁ hom₂ z hz₁ hz₂

theorem exists_compOp
    {E A C : Scheme.{0}}
    {fE : E ⟶ Spec (CommRingCat.of R)} {fA : A ⟶ Spec (CommRingCat.of R)} {fC : C ⟶ Spec (CommRingCat.of R)}
    {LE : RelativeGroupLaw R fE} {LA : RelativeGroupLaw R fA} {LC : RelativeGroupLaw R fC}
    (D₁ : HomRep fE fA LE LA) (D₂ : HomRep fA fC LA LC) (D₃ : HomRep fE fC LE LC)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R)) (q₁ : X ⟶ D₁.H) (q₂ : X ⟶ D₂.H)
    (hq₁ : q₁ ≫ D₁.πH = πX) (hq₂ : q₂ ≫ D₂.πH = πX) :
    ∃ comp : X ⟶ D₃.H, comp ≫ D₃.πH = πX ∧
      ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback fE s ⟶ A) (hφ : φ ≫ fA = pullback.snd fE s ≫ s)
        (φ' : pullback fA s ⟶ C) (hφ' : φ' ≫ fC = pullback.snd fA s ≫ s),
        IsHom fE fA LE LA s φ hφ → IsHom fA fC LA LC s φ' hφ' →
        ∀ z : SchemeHomOver s πX, z.1 ≫ q₁ = (D₁.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D₂.pt S' s φ' hφ').1 →
          z.1 ≫ comp = (D₃.pt S' s (pullback.lift φ (pullback.snd fE s) hφ ≫ φ')
            (by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd])).1 := by
  have hFnat : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
      (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
      (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
      (φ₁ : pullback fE s ⟶ A) (hφ₁ : φ₁ ≫ fA = pullback.snd fE s ≫ s)
      (φ₂ : pullback fA s ⟶ C) (hφ₂ : φ₂ ≫ fC = pullback.snd fA s ≫ s),
      pullback.lift (BC fE ψ s s'' hs φ₁) (pullback.snd fE s'') (BC_over fE fA ψ s s'' hs φ₁ hφ₁) ≫ BC fA ψ s s'' hs φ₂ =
        BC fE ψ s s'' hs (pullback.lift φ₁ (pullback.snd fE s) hφ₁ ≫ φ₂) := by
    intro S' S'' _ _ ψ s s'' hs φ₁ hφ₁ φ₂ hφ₂
    unfold BC
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  obtain ⟨op, hop, hsem⟩ := exists_op₂ D₁ D₂ D₃ X πX q₁ q₂ hq₁ hq₂
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ => pullback.lift φ₁ (pullback.snd fE s) hφ₁ ≫ φ₂)
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ => by rw [Category.assoc, hφ₂, ← Category.assoc, pullback.lift_snd])
    hFnat
  exact ⟨op, hop, hsem⟩

theorem exists_constOp (D₁ : HomRep f₁ g₁ L₁ M₁) (D₂ : HomRep f₂ g₂ L₂ M₂) (D₃ : HomRep f₃ g₃ L₃ M₃)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R)) (q₁ : X ⟶ D₁.H) (q₂ : X ⟶ D₂.H)
    (hq₁ : q₁ ≫ D₁.πH = πX) (hq₂ : q₂ ≫ D₂.πH = πX)
    (u : A₃ ⟶ B₃) (hu : u ≫ g₃ = f₃) :
    ∃ cst : X ⟶ D₃.H, cst ≫ D₃.πH = πX ∧
      ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver s πX),
        z.1 ≫ cst = (D₃.pt S' s (pullback.fst f₃ s ≫ u) (by rw [Category.assoc, hu]; exact pullback.condition)).1 := by
  obtain ⟨op, hop, hsem⟩ := exists_op₂ D₁ D₂ D₃ X πX q₁ q₂ hq₁ hq₂
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ => pullback.fst f₃ s ≫ u)
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ => by rw [Category.assoc, hu]; exact pullback.condition)
    (fun S' S'' _ _ ψ s s'' hs φ₁ hφ₁ φ₂ hφ₂ => by unfold BC; rw [← Category.assoc, pullback.lift_fst])
  refine ⟨op, hop, ?_⟩
  intro S' _ s z
  have hco₁ : (z.1 ≫ q₁) ≫ D₁.πH = s := by rw [Category.assoc, hq₁]; exact z.2
  obtain ⟨φ₁, hφ₁, hom₁, hpt₁⟩ := D₁.surj S' s ⟨z.1 ≫ q₁, hco₁⟩
  have hz₁ : z.1 ≫ q₁ = (D₁.pt S' s φ₁ hφ₁).1 := by rw [hpt₁]
  exact sem₁_of_sem₂ D₁ D₂ D₃ X πX q₁ q₂ hq₂ (fun S' _ s φ₁ hφ₁ => pullback.fst f₃ s ≫ u)
    (fun S' _ s φ₁ hφ₁ => by rw [Category.assoc, hu]; exact pullback.condition) op hsem S' s φ₁ hφ₁ hom₁ z hz₁

theorem exists_precompOp (D₁ : HomRep f₁ g₁ L₁ M₁) (D₂ : HomRep f₂ g₂ L₂ M₂)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R)) (q₁ : X ⟶ D₁.H) (q₂ : X ⟶ D₂.H)
    (hq₁ : q₁ ≫ D₁.πH = πX) (hq₂ : q₂ ≫ D₂.πH = πX)
    (u : A₁ ⟶ A₁) (hu : u ≫ f₁ = f₁) :
    ∃ pre : X ⟶ D₁.H, pre ≫ D₁.πH = πX ∧
      ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback f₁ s ⟶ B₁) (hφ : φ ≫ g₁ = pullback.snd f₁ s ≫ s), IsHom f₁ g₁ L₁ M₁ s φ hφ →
        ∀ z : SchemeHomOver s πX, z.1 ≫ q₁ = (D₁.pt S' s φ hφ).1 →
          z.1 ≫ pre = (D₁.pt S' s
            (pullback.lift (pullback.fst f₁ s ≫ u) (pullback.snd f₁ s) (by rw [Category.assoc, hu]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd])).1 := by
  have hFnat : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
      (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
      (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
      (φ₁ : pullback f₁ s ⟶ B₁) (hφ₁ : φ₁ ≫ g₁ = pullback.snd f₁ s ≫ s)
      (φ₂ : pullback f₂ s ⟶ B₂) (hφ₂ : φ₂ ≫ g₂ = pullback.snd f₂ s ≫ s),
      pullback.lift (pullback.fst f₁ s'' ≫ u) (pullback.snd f₁ s'') (by rw [Category.assoc, hu]; exact pullback.condition) ≫
          BC f₁ ψ s s'' hs φ₁ =
        BC f₁ ψ s s'' hs (pullback.lift (pullback.fst f₁ s ≫ u) (pullback.snd f₁ s)
          (by rw [Category.assoc, hu]; exact pullback.condition) ≫ φ₁) := by
    intro S' S'' _ _ ψ s s'' hs φ₁ hφ₁ φ₂ hφ₂
    unfold BC
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  obtain ⟨op, hop, hsem⟩ := exists_op₂ D₁ D₂ D₁ X πX q₁ q₂ hq₁ hq₂
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ =>
      pullback.lift (pullback.fst f₁ s ≫ u) (pullback.snd f₁ s) (by rw [Category.assoc, hu]; exact pullback.condition) ≫ φ₁)
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ => by rw [Category.assoc, hφ₁, ← Category.assoc, pullback.lift_snd])
    hFnat
  refine ⟨op, hop, ?_⟩
  exact sem₁_of_sem₂ D₁ D₂ D₁ X πX q₁ q₂ hq₂
    (fun S' _ s φ₁ hφ₁ =>
      pullback.lift (pullback.fst f₁ s ≫ u) (pullback.snd f₁ s) (by rw [Category.assoc, hu]; exact pullback.condition) ≫ φ₁)
    (fun S' _ s φ₁ hφ₁ => by rw [Category.assoc, hφ₁, ← Category.assoc, pullback.lift_snd]) op hsem

theorem exists_postcompOp (D₁ : HomRep f₁ g₁ L₁ M₁) (D₂ : HomRep f₂ g₂ L₂ M₂)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R)) (q₁ : X ⟶ D₁.H) (q₂ : X ⟶ D₂.H)
    (hq₁ : q₁ ≫ D₁.πH = πX) (hq₂ : q₂ ≫ D₂.πH = πX)
    (v : B₁ ⟶ B₁) (hv : v ≫ g₁ = g₁) :
    ∃ post : X ⟶ D₁.H, post ≫ D₁.πH = πX ∧
      ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback f₁ s ⟶ B₁) (hφ : φ ≫ g₁ = pullback.snd f₁ s ≫ s), IsHom f₁ g₁ L₁ M₁ s φ hφ →
        ∀ z : SchemeHomOver s πX, z.1 ≫ q₁ = (D₁.pt S' s φ hφ).1 →
          z.1 ≫ post = (D₁.pt S' s (φ ≫ v) (by rw [Category.assoc, hv, hφ])).1 := by
  obtain ⟨op, hop, hsem⟩ := exists_op₂ D₁ D₂ D₁ X πX q₁ q₂ hq₁ hq₂
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ => φ₁ ≫ v)
    (fun S' _ s φ₁ hφ₁ φ₂ hφ₂ => by rw [Category.assoc, hv, hφ₁])
    (fun S' S'' _ _ ψ s s'' hs φ₁ hφ₁ φ₂ hφ₂ => by (try dsimp only); unfold BC; simp only [Category.assoc])
  refine ⟨op, hop, ?_⟩
  exact sem₁_of_sem₂ D₁ D₂ D₁ X πX q₁ q₂ hq₂ (fun S' _ s φ₁ hφ₁ => φ₁ ≫ v)
    (fun S' _ s φ₁ hφ₁ => by rw [Category.assoc, hv, hφ₁]) op hsem

end Instances

theorem exists_equaliserLocus₄
    {B P H₁ H₂ H₃ H₄ : Scheme.{0}}
    (πP : P ⟶ B) (π₁ : H₁ ⟶ B) (π₂ : H₂ ⟶ B) (π₃ : H₃ ⟶ B) (π₄ : H₄ ⟶ B)
    (hPsep : IsSeparated πP) (hPlft : LocallyOfFiniteType πP) (hPlfp : LocallyOfFinitePresentation πP)
    (h₁sep : IsSeparated π₁) (h₁lft : LocallyOfFiniteType π₁)
    (h₂sep : IsSeparated π₂) (h₂lft : LocallyOfFiniteType π₂)
    (h₃sep : IsSeparated π₃) (h₃lft : LocallyOfFiniteType π₃)
    (h₄sep : IsSeparated π₄) (h₄lft : LocallyOfFiniteType π₄)
    {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄]
    (a₁ b₁ : ι₁ → (P ⟶ H₁)) (ha₁ : ∀ i, a₁ i ≫ π₁ = πP) (hb₁ : ∀ i, b₁ i ≫ π₁ = πP)
    (a₂ b₂ : ι₂ → (P ⟶ H₂)) (ha₂ : ∀ i, a₂ i ≫ π₂ = πP) (hb₂ : ∀ i, b₂ i ≫ π₂ = πP)
    (a₃ b₃ : ι₃ → (P ⟶ H₃)) (ha₃ : ∀ i, a₃ i ≫ π₃ = πP) (hb₃ : ∀ i, b₃ i ≫ π₃ = πP)
    (a₄ b₄ : ι₄ → (P ⟶ H₄)) (ha₄ : ∀ i, a₄ i ≫ π₄ = πP) (hb₄ : ∀ i, b₄ i ≫ π₄ = πP) :
    ∃ (X : Scheme.{0}) (m : X ⟶ P), IsClosedImmersion m ∧
      (∀ i, m ≫ a₁ i = m ≫ b₁ i) ∧ (∀ i, m ≫ a₂ i = m ≫ b₂ i) ∧
      (∀ i, m ≫ a₃ i = m ≫ b₃ i) ∧ (∀ i, m ≫ a₄ i = m ≫ b₄ i) ∧
      (∀ (T : Scheme.{0}) (g : T ⟶ P), (∀ i, g ≫ a₁ i = g ≫ b₁ i) → (∀ i, g ≫ a₂ i = g ≫ b₂ i) →
        (∀ i, g ≫ a₃ i = g ≫ b₃ i) → (∀ i, g ≫ a₄ i = g ≫ b₄ i) → ∃! g' : T ⟶ X, g' ≫ m = g) ∧
      IsSeparated (m ≫ πP) ∧ LocallyOfFiniteType (m ≫ πP) ∧ LocallyOfFinitePresentation (m ≫ πP) := by
  classical
  haveI := hPsep; haveI := hPlft; haveI := hPlfp
  haveI := h₁sep; haveI := h₁lft; haveI := h₂sep; haveI := h₂lft
  haveI := h₃sep; haveI := h₃lft; haveI := h₄sep; haveI := h₄lft

  obtain ⟨E₁, m₁, hci₁, heq₁, huniv₁, hlfp₁⟩ :=
    AlgebraicGeometry.exists_equalizerLocus_isClosedImmersion_of_isSeparated πP π₁ h₁sep a₁ b₁ ha₁ hb₁
  haveI := hci₁
  haveI : LocallyOfFinitePresentation m₁ :=
    hlfp₁ (AlgebraicGeometry.locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType π₁)

  obtain ⟨E₂, m₂, hci₂, heq₂, huniv₂, hlfp₂⟩ :=
    AlgebraicGeometry.exists_equalizerLocus_isClosedImmersion_of_isSeparated (m₁ ≫ πP) π₂ h₂sep
      (fun i => m₁ ≫ a₂ i) (fun i => m₁ ≫ b₂ i)
      (fun i => by rw [Category.assoc, ha₂]) (fun i => by rw [Category.assoc, hb₂])
  haveI := hci₂
  haveI : LocallyOfFinitePresentation m₂ :=
    hlfp₂ (AlgebraicGeometry.locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType π₂)

  obtain ⟨E₃, m₃, hci₃, heq₃, huniv₃, hlfp₃⟩ :=
    AlgebraicGeometry.exists_equalizerLocus_isClosedImmersion_of_isSeparated (m₂ ≫ m₁ ≫ πP) π₃ h₃sep
      (fun i => m₂ ≫ m₁ ≫ a₃ i) (fun i => m₂ ≫ m₁ ≫ b₃ i)
      (fun i => by simp only [Category.assoc, ha₃]) (fun i => by simp only [Category.assoc, hb₃])
  haveI := hci₃
  haveI : LocallyOfFinitePresentation m₃ :=
    hlfp₃ (AlgebraicGeometry.locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType π₃)

  obtain ⟨E₄, m₄, hci₄, heq₄, huniv₄, hlfp₄⟩ :=
    AlgebraicGeometry.exists_equalizerLocus_isClosedImmersion_of_isSeparated (m₃ ≫ m₂ ≫ m₁ ≫ πP) π₄ h₄sep
      (fun i => m₃ ≫ m₂ ≫ m₁ ≫ a₄ i) (fun i => m₃ ≫ m₂ ≫ m₁ ≫ b₄ i)
      (fun i => by simp only [Category.assoc, ha₄]) (fun i => by simp only [Category.assoc, hb₄])
  haveI := hci₄
  haveI : LocallyOfFinitePresentation m₄ :=
    hlfp₄ (AlgebraicGeometry.locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType π₄)
  refine ⟨E₄, m₄ ≫ m₃ ≫ m₂ ≫ m₁, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simp only [Category.assoc]; rw [heq₁ i]
  · intro i; simp only [Category.assoc]; rw [heq₂ i]
  · intro i; simp only [Category.assoc]; rw [heq₃ i]
  · intro i
    have := heq₄ i
    simp only [Category.assoc] at this ⊢
    exact this
  · intro T g hg₁ hg₂ hg₃ hg₄
    have key : ∀ {T' E P' H : Scheme.{0}} {n : E ⟶ P'} {gk : T' ⟶ E} {g0 : T' ⟶ P'} (_ : gk ≫ n = g0)
        {a b : P' ⟶ H}, g0 ≫ a = g0 ≫ b → gk ≫ n ≫ a = gk ≫ n ≫ b := by
      intro T' E P' H n gk g0 e a b h
      subst e
      simpa only [Category.assoc] using h
    obtain ⟨g₁, hg₁m, -⟩ := huniv₁ T g hg₁
    obtain ⟨g₂, hg₂m, -⟩ := huniv₂ T g₁ (fun i => key hg₁m (hg₂ i))
    have e₂ : g₂ ≫ m₂ ≫ m₁ = g := by rw [← Category.assoc, hg₂m, hg₁m]
    obtain ⟨g₃, hg₃m, -⟩ := huniv₃ T g₂ (fun i => by
      have := key e₂ (hg₃ i); simpa only [Category.assoc] using this)
    have e₃ : g₃ ≫ m₃ ≫ m₂ ≫ m₁ = g := by rw [← Category.assoc, hg₃m]; exact e₂
    obtain ⟨g₄, hg₄m, -⟩ := huniv₄ T g₃ (fun i => by
      have := key e₃ (hg₄ i); simpa only [Category.assoc] using this)
    have hX : g₄ ≫ m₄ ≫ m₃ ≫ m₂ ≫ m₁ = g := by rw [← Category.assoc, hg₄m]; exact e₃
    refine ⟨g₄, hX, fun g' hg' => ?_⟩
    rw [← cancel_mono (m₄ ≫ m₃ ≫ m₂ ≫ m₁), hX]
    exact hg'
  · infer_instance
  · infer_instance
  · infer_instance

theorem sep_lft_lfp_pullback {B H H' : Scheme.{0}} (π : H ⟶ B) (π' : H' ⟶ B)
    (h₁ : IsSeparated π) (h₂ : LocallyOfFiniteType π) (h₃ : LocallyOfFinitePresentation π)
    (h₁' : IsSeparated π') (h₂' : LocallyOfFiniteType π') (h₃' : LocallyOfFinitePresentation π') :
    IsSeparated (pullback.fst π π' ≫ π) ∧ LocallyOfFiniteType (pullback.fst π π' ≫ π) ∧
      LocallyOfFinitePresentation (pullback.fst π π' ≫ π) := by
  haveI := h₁; haveI := h₂; haveI := h₃; haveI := h₁'; haveI := h₂'; haveI := h₃'
  haveI : IsSeparated (pullback.fst π π') := MorphismProperty.pullback_fst _ _ h₁'
  haveI : LocallyOfFiniteType (pullback.fst π π') := MorphismProperty.pullback_fst _ _ h₂'
  haveI : LocallyOfFinitePresentation (pullback.fst π π') := MorphismProperty.pullback_fst _ _ h₃'
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section FEC

open scoped TensorProduct Quaternion
open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem exists_product_and_relOps
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve.{0} Λ N S)
    {ι : Type} (β : ι → ↥Λ)
    (D_EA : HomRep E.f A.f E.L A.L) (D_AE : HomRep A.f E.f A.L E.L)
    (D_EE : HomRep E.f E.f E.L E.L) (D_AA : HomRep A.f A.f A.L A.L)
    (hsepEA : IsSeparated D_EA.πH) (hlftEA : LocallyOfFiniteType D_EA.πH) (hlfpEA : LocallyOfFinitePresentation D_EA.πH)
    (hsepAE : IsSeparated D_AE.πH) (hlftAE : LocallyOfFiniteType D_AE.πH) (hlfpAE : LocallyOfFinitePresentation D_AE.πH) :
    ∃ (P : Scheme.{0}) (πP : P ⟶ Spec (CommRingCat.of S)) (q₁ : P ⟶ D_EA.H) (q₂ : P ⟶ D_AE.H)
      (aE bE : ι → (P ⟶ D_EA.H)) (aA bA : ι → (P ⟶ D_AE.H))
      (cE kE : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ → (P ⟶ D_EE.H))
      (cA kA : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ → (P ⟶ D_AA.H)),
      q₁ ≫ D_EA.πH = πP ∧ q₂ ≫ D_AE.πH = πP ∧
      (∀ (T : Scheme.{0}) (g₁ : T ⟶ D_EA.H) (g₂ : T ⟶ D_AE.H), g₁ ≫ D_EA.πH = g₂ ≫ D_AE.πH →
      ∃! G : T ⟶ P, G ≫ q₁ = g₁ ∧ G ≫ q₂ = g₂) ∧
      IsSeparated πP ∧ LocallyOfFiniteType πP ∧ LocallyOfFinitePresentation πP ∧
      (∀ i, aE i ≫ D_EA.πH = πP) ∧ (∀ i, bE i ≫ D_EA.πH = πP) ∧
      (∀ i, aA i ≫ D_AE.πH = πP) ∧ (∀ i, bA i ≫ D_AE.πH = πP) ∧
      (∀ hd, cE hd ≫ D_EE.πH = πP) ∧ (∀ hd, kE hd ≫ D_EE.πH = πP) ∧
      (∀ hd, cA hd ≫ D_AA.πH = πP) ∧ (∀ hd, kA hd ≫ D_AA.πH = πP) ∧

      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ aE i = (D_EA.pt S' s (pullback.lift (pullback.fst E.f s ≫ E.act (β i)) (pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd])).1) ∧

      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ bE i = (D_EA.pt S' s (φ ≫ A.act (β i)) (by rw [Category.assoc, A.act_over, hφ])).1) ∧

      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ aA i = (D_AE.pt S' s (pullback.lift (pullback.fst A.f s ≫ A.act (β i)) (pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact pullback.condition) ≫ φ') (by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd])).1) ∧

      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ bA i = (D_AE.pt S' s (φ' ≫ E.act (β i)) (by rw [Category.assoc, E.act_over, hφ'])).1) ∧

      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ cE hd = (D_EE.pt S' s (pullback.lift φ (pullback.snd E.f s) hφ ≫ φ') (by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd])).1) ∧

      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ kE hd = (D_EE.pt S' s (pullback.fst E.f s ≫ E.act ⟨_, hd⟩) (by rw [Category.assoc, E.act_over]; exact pullback.condition)).1) ∧

      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ cA hd = (D_AA.pt S' s (pullback.lift φ' (pullback.snd A.f s) hφ' ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd])).1) ∧

      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ kA hd = (D_AA.pt S' s (pullback.fst A.f s ≫ A.act ⟨_, hd⟩) (by rw [Category.assoc, A.act_over]; exact pullback.condition)).1) := by
  classical
  let P : Scheme.{0} := pullback D_EA.πH D_AE.πH
  let q₁ : P ⟶ D_EA.H := pullback.fst D_EA.πH D_AE.πH
  let q₂ : P ⟶ D_AE.H := pullback.snd D_EA.πH D_AE.πH
  let πP : P ⟶ Spec (CommRingCat.of S) := q₁ ≫ D_EA.πH
  have hq₁ : q₁ ≫ D_EA.πH = πP := rfl
  have hq₂ : q₂ ≫ D_AE.πH = πP := pullback.condition.symm
  have hP : ∀ (T : Scheme.{0}) (g₁ : T ⟶ D_EA.H) (g₂ : T ⟶ D_AE.H), g₁ ≫ D_EA.πH = g₂ ≫ D_AE.πH →
      ∃! G : T ⟶ P, G ≫ q₁ = g₁ ∧ G ≫ q₂ = g₂ := by
    intro T g₁ g₂ h
    refine ⟨pullback.lift g₁ g₂ h, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
    rintro G ⟨hG₁, hG₂⟩
    apply pullback.hom_ext
    · rw [hG₁, pullback.lift_fst]
    · rw [hG₂, pullback.lift_snd]

  have XaE := fun i => exists_precompOp D_EA D_AE P πP q₁ q₂ hq₁ hq₂ (E.act (β i)) (E.act_over (β i))
  have XbE := fun i => exists_postcompOp D_EA D_AE P πP q₁ q₂ hq₁ hq₂ (A.act (β i)) (A.act_over (β i))
  have XaA := fun i => exists_precompOp D_AE D_EA P πP q₂ q₁ hq₂ hq₁ (A.act (β i)) (A.act_over (β i))
  have XbA := fun i => exists_postcompOp D_AE D_EA P πP q₂ q₁ hq₂ hq₁ (E.act (β i)) (E.act_over (β i))
  have XcE := exists_compOp D_EA D_AE D_EE P πP q₁ q₂ hq₁ hq₂
  have XcA := exists_compOp D_AE D_EA D_AA P πP q₂ q₁ hq₂ hq₁
  have XkE := fun (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) =>
    exists_constOp D_EA D_AE D_EE P πP q₁ q₂ hq₁ hq₂ (E.act ⟨_, hd⟩) (E.act_over ⟨_, hd⟩)
  have XkA := fun (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) =>
    exists_constOp D_EA D_AE D_AA P πP q₁ q₂ hq₁ hq₂ (A.act ⟨_, hd⟩) (A.act_over ⟨_, hd⟩)
  choose aE haE₀ haE₁ using XaE
  choose bE hbE₀ hbE₁ using XbE
  choose aA haA₀ haA₁ using XaA
  choose bA hbA₀ hbA₁ using XbA
  obtain ⟨cE, hcE₀, hcE₁⟩ := XcE
  obtain ⟨cA, hcA₀, hcA₁⟩ := XcA
  choose kE hkE₀ hkE₁ using XkE
  choose kA hkA₀ hkA₁ using XkA
  obtain ⟨hPsep, hPlft, hPlfp⟩ := sep_lft_lfp_pullback D_EA.πH D_AE.πH hsepEA hlftEA hlfpEA hsepAE hlftAE hlfpAE
  refine ⟨P, πP, q₁, q₂, aE, bE, aA, bA, fun _ => cE, kE, fun _ => cA, kA, hq₁, hq₂, hP, hPsep, hPlft, hPlfp,
    haE₀, hbE₀, haA₀, hbA₀, fun _ => hcE₀, hkE₀, fun _ => hcA₀, hkA₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact haE₁ i S' s φ hφ h₁ z hz₁
  · intro i S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact hbE₁ i S' s φ hφ h₁ z hz₁
  · intro i S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact haA₁ i S' s φ' hφ' h₂ z hz₂
  · intro i S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact hbA₁ i S' s φ' hφ' h₂ z hz₂
  · intro hd S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact hcE₁ S' s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
  · intro hd S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact hkE₁ hd S' s z
  · intro hd S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact hcA₁ S' s φ' hφ' φ hφ h₂ h₁ z hz₂ hz₁
  · intro hd S' _ s φ hφ φ' hφ' h₁ h₂ z hz₁ hz₂
    exact hkA₁ hd S' s z

theorem exists_pairLocus_data
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve.{0} Λ N S)
    {ι : Type} [Fintype ι] (β : ι → ↥Λ)
    (D_EA : HomRep E.f A.f E.L A.L) (D_AE : HomRep A.f E.f A.L E.L)
    (D_EE : HomRep E.f E.f E.L E.L) (D_AA : HomRep A.f A.f A.L A.L)
    (hsepEA : IsSeparated D_EA.πH) (hlftEA : LocallyOfFiniteType D_EA.πH) (hlfpEA : LocallyOfFinitePresentation D_EA.πH)
    (hsepAE : IsSeparated D_AE.πH) (hlftAE : LocallyOfFiniteType D_AE.πH) (hlfpAE : LocallyOfFinitePresentation D_AE.πH)
    (hsepEE : IsSeparated D_EE.πH) (hlftEE : LocallyOfFiniteType D_EE.πH)
    (hsepAA : IsSeparated D_AA.πH) (hlftAA : LocallyOfFiniteType D_AA.πH) :
    ∃ (P : Scheme.{0}) (πP : P ⟶ Spec (CommRingCat.of S)) (q₁ : P ⟶ D_EA.H) (q₂ : P ⟶ D_AE.H)
      (aE bE : ι → (P ⟶ D_EA.H)) (aA bA : ι → (P ⟶ D_AE.H))
      (cE kE : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ → (P ⟶ D_EE.H))
      (cA kA : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ → (P ⟶ D_AA.H))
      (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of S)) (m : X ⟶ P),
      q₁ ≫ D_EA.πH = πP ∧ q₂ ≫ D_AE.πH = πP ∧
      (∀ (T : Scheme.{0}) (g₁ : T ⟶ D_EA.H) (g₂ : T ⟶ D_AE.H), g₁ ≫ D_EA.πH = g₂ ≫ D_AE.πH →
      ∃! G : T ⟶ P, G ≫ q₁ = g₁ ∧ G ≫ q₂ = g₂) ∧
      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ aE i = (D_EA.pt S' s (pullback.lift (pullback.fst E.f s ≫ E.act (β i)) (pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd])).1) ∧
      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ bE i = (D_EA.pt S' s (φ ≫ A.act (β i)) (by rw [Category.assoc, A.act_over, hφ])).1) ∧
      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ aA i = (D_AE.pt S' s (pullback.lift (pullback.fst A.f s ≫ A.act (β i)) (pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact pullback.condition) ≫ φ') (by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd])).1) ∧
      (∀ (i : ι) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ bA i = (D_AE.pt S' s (φ' ≫ E.act (β i)) (by rw [Category.assoc, E.act_over, hφ'])).1) ∧
      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ cE hd = (D_EE.pt S' s (pullback.lift φ (pullback.snd E.f s) hφ ≫ φ') (by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd])).1) ∧
      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ kE hd = (D_EE.pt S' s (pullback.fst E.f s ≫ E.act ⟨_, hd⟩) (by rw [Category.assoc, E.act_over]; exact pullback.condition)).1) ∧
      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ cA hd = (D_AA.pt S' s (pullback.lift φ' (pullback.snd A.f s) hφ' ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd])).1) ∧
      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ z : SchemeHomOver s πP, z.1 ≫ q₁ = (D_EA.pt S' s φ hφ).1 → z.1 ≫ q₂ = (D_AE.pt S' s φ' hφ').1 →
        z.1 ≫ kA hd = (D_AA.pt S' s (pullback.fst A.f s ≫ A.act ⟨_, hd⟩) (by rw [Category.assoc, A.act_over]; exact pullback.condition)).1) ∧
      Mono m ∧ m ≫ πP = πX ∧
      (∀ i : ι, m ≫ aE i = m ≫ bE i) ∧ (∀ i : ι, m ≫ aA i = m ≫ bA i) ∧
      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ), m ≫ cE hd = m ≫ kE hd) ∧
      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ), m ≫ cA hd = m ≫ kA hd) ∧
      (∀ (T : Scheme.{0}) (g : T ⟶ P), (∀ i : ι, g ≫ aE i = g ≫ bE i) → (∀ i : ι, g ≫ aA i = g ≫ bA i) →
      (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ), g ≫ cE hd = g ≫ kE hd) → (∀ (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ), g ≫ cA hd = g ≫ kA hd) → ∃ g' : T ⟶ X, g' ≫ m = g) ∧
      IsSeparated πX ∧ LocallyOfFiniteType πX ∧ LocallyOfFinitePresentation πX := by
  classical
  obtain ⟨P, πP, q₁, q₂, aE, bE, aA, bA, cE, kE, cA, kA, hq₁, hq₂, hP, hPsep, hPlft, hPlfp,
      oaE, obE, oaA, obA, ocE, okE, ocA, okA, haE, hbE, haA, hbA, hcE, hkE, hcA, hkA⟩ :=
    exists_product_and_relOps r d S E A β D_EA D_AE D_EE D_AA hsepEA hlftEA hlfpEA hsepAE hlftAE hlfpAE
  obtain ⟨X, m, hci, heq₁, heq₂, heq₃, heq₄, huniv, hXsep, hXlft, hXlfp⟩ :=
    exists_equaliserLocus₄ πP D_EA.πH D_AE.πH D_EE.πH D_AA.πH hPsep hPlft hPlfp
      hsepEA hlftEA hsepAE hlftAE hsepEE hlftEE hsepAA hlftAA
      aE bE oaE obE aA bA oaA obA
      (fun x : PLift ((((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) => cE x.down) (fun x => kE x.down) (fun x => ocE x.down) (fun x => okE x.down)
      (fun x : PLift ((((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) => cA x.down) (fun x => kA x.down) (fun x => ocA x.down) (fun x => okA x.down)
  haveI := hci
  refine ⟨P, πP, q₁, q₂, aE, bE, aA, bA, cE, kE, cA, kA, X, m ≫ πP, m, hq₁, hq₂, hP,
    haE, hbE, haA, hbA, hcE, hkE, hcA, hkA, inferInstance, rfl, heq₁, heq₂,
    fun hd => heq₃ ⟨hd⟩, fun hd => heq₄ ⟨hd⟩, ?_, hXsep, hXlft, hXlfp⟩
  intro T g h1 h2 h3 h4
  exact (huniv T g h1 h2 (fun x => h3 x.down) (fun x => h4 x.down)).exists

theorem exists_homRep (S : Type) [CommRing S] {A B : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (g : B ⟶ Spec (CommRingCat.of S))
    (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    (𝓛A : A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A f)
    (𝓛B : B.Modules) (hB₁ : Scheme.Modules.IsInvertible 𝓛B) (hB₂ : Scheme.Modules.ClosedImmersionBySections 𝓛B g) :
    ∃ D : HomRep f g LA LB, IsSeparated D.πH ∧ LocallyOfFiniteType D.πH ∧ LocallyOfFinitePresentation D.πH := by
  obtain ⟨H, πH, pt, hnat, hsurj, hinj, hsep, hlft, hlfp, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_of_closedImmersionBySections_lfp
      S f g LA LB hAc hBc hA hB 𝓛A hA₁ hA₂ 𝓛B hB₁ hB₂
  exact ⟨⟨H, πH, pt, hnat, hsurj, hinj⟩, hsep, hlft, hlfp⟩

theorem isHom_liftComp {S : Type} [CommRing S] {AX AY AZ : Scheme.{0}}
    {fX : AX ⟶ Spec (CommRingCat.of S)} {fY : AY ⟶ Spec (CommRingCat.of S)} {fZ : AZ ⟶ Spec (CommRingCat.of S)}
    (LX : RelativeGroupLaw S fX) (LY : RelativeGroupLaw S fY) (LZ : RelativeGroupLaw S fZ)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (χ : pullback fX s ⟶ AY) (hχ : χ ≫ fY = pullback.snd fX s ≫ s)
    (ω : pullback fY s ⟶ AZ) (hω : ω ≫ fZ = pullback.snd fY s ≫ s)
    (hχh : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) fX),
        pullback.lift (LX.mul (t' ≫ s) P Q).1 t' (LX.mul (t' ≫ s) P Q).2 ≫ χ =
          (LY.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩).1))
    (hωh : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) fY),
        pullback.lift (LY.mul (t' ≫ s) P Q).1 t' (LY.mul (t' ≫ s) P Q).2 ≫ ω =
          (LZ.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩).1))
    (κ : pullback fX s ⟶ AZ) (hκ : κ ≫ fZ = pullback.snd fX s ≫ s)
    (e : κ = pullback.lift χ (pullback.snd fX s) hχ ≫ ω) :
    (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) fX),
        pullback.lift (LX.mul (t' ≫ s) P Q).1 t' (LX.mul (t' ≫ s) P Q).2 ≫ κ =
          (LZ.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩).1) := by
  subst e
  intro T t' P Q
  have mulcongr : ∀ (U V U' V' : SchemeHomOver (t' ≫ s) fZ), U = U' → V = V' →
      (LZ.mul (t' ≫ s) U V).1 = (LZ.mul (t' ≫ s) U' V').1 := by
    rintro _ _ _ _ rfl rfl; rfl
  have h1 : pullback.lift (LX.mul (t' ≫ s) P Q).1 t' (LX.mul (t' ≫ s) P Q).2 ≫ pullback.lift χ (pullback.snd fX s) hχ =
      pullback.lift
        (LY.mul (t' ≫ s)
          ⟨pullback.lift P.1 t' P.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩
          ⟨pullback.lift Q.1 t' Q.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩).1 t'
        (LY.mul (t' ≫ s)
          ⟨pullback.lift P.1 t' P.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩
          ⟨pullback.lift Q.1 t' Q.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩).2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact hχh T t' P Q
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  rw [← Category.assoc, h1, hωh T t']
  refine mulcongr _ _ _ _ (Subtype.ext ?_) (Subtype.ext ?_)
  · show pullback.lift (pullback.lift P.1 t' P.2 ≫ χ) t' _ ≫ ω =
        pullback.lift P.1 t' P.2 ≫ pullback.lift χ (pullback.snd fX s) hχ ≫ ω
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
  · show pullback.lift (pullback.lift Q.1 t' Q.2 ≫ χ) t' _ ≫ ω =
        pullback.lift Q.1 t' Q.2 ≫ pullback.lift χ (pullback.snd fX s) hχ ≫ ω
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]

theorem isHom_fst_comp_endo {S : Type} [CommRing S] {AX : Scheme.{0}} {fX : AX ⟶ Spec (CommRingCat.of S)}
    (LX : RelativeGroupLaw S fX) (u : AX ⟶ AX) (hu : u ≫ fX = fX)
    (huh : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t fX),
      mapPt u hu (LX.mul t P Q) = LX.mul t (mapPt u hu P) (mapPt u hu Q))
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (κ : pullback fX s ⟶ AX) (hκ : κ ≫ fX = pullback.snd fX s ≫ s) (e : κ = pullback.fst fX s ≫ u) :
    (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) fX),
        pullback.lift (LX.mul (t' ≫ s) P Q).1 t' (LX.mul (t' ≫ s) P Q).2 ≫ κ =
          (LX.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩).1) := by
  subst e
  intro T t' P Q
  have mulcongr : ∀ (U V U' V' : SchemeHomOver (t' ≫ s) fX), U = U' → V = V' →
      (LX.mul (t' ≫ s) U V).1 = (LX.mul (t' ≫ s) U' V').1 := by
    rintro _ _ _ _ rfl rfl; rfl
  have h := congrArg Subtype.val (huh (t' ≫ s) P Q)
  simp only [mapPt_coe] at h
  rw [← Category.assoc, pullback.lift_fst, h]
  refine mulcongr _ _ _ _ (Subtype.ext ?_) (Subtype.ext ?_)
  · show P.1 ≫ u = pullback.lift P.1 t' P.2 ≫ pullback.fst fX s ≫ u
    rw [← Category.assoc, pullback.lift_fst]
  · show Q.1 ≫ u = pullback.lift Q.1 t' Q.2 ≫ pullback.fst fX s ≫ u
    rw [← Category.assoc, pullback.lift_fst]

end FEC

end PairEq

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j) (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (𝓛E : E.A.Modules) (hE₁ : Scheme.Modules.IsInvertible 𝓛E) (hE₂ : Scheme.Modules.ClosedImmersionBySections 𝓛E E.f)
    (𝓛A : A.A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A A.f) :
    ∃ (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
        (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1) →
        ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩)) →
          SchemeHomOver s πX),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩)))
          (φ₂ : Limits.pullback E.f s'' ⟶ A.A) (hφ₂ : φ₂ ≫ A.f = Limits.pullback.snd E.f s'' ≫ s'')
          (φ₂' : Limits.pullback A.f s'' ⟶ E.A) (hφ₂' : φ₂' ≫ E.f = Limits.pullback.snd A.f s'' ≫ s'')
          (k₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s'') P Q).1 t' (E.L.mul (t' ≫ s'') P Q).2 ≫ φ₂ =
              (A.L.mul (t' ≫ s'')
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ₂, by rw [Category.assoc, hφ₂, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ₂, by rw [Category.assoc, hφ₂, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s'') P Q).1 t' (A.L.mul (t' ≫ s'') P Q).2 ≫ φ₂' =
              (E.L.mul (t' ≫ s'')
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ₂', by rw [Category.assoc, hφ₂', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ₂', by rw [Category.assoc, hφ₂', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s'' ≫ E.act (β i)) (Limits.pullback.snd E.f s'')
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ₂ = φ₂ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s'' ≫ A.act (β i)) (Limits.pullback.snd A.f s'')
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ₂' = φ₂' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ₂ (Limits.pullback.snd E.f s'') hφ₂ ≫ φ₂' = Limits.pullback.fst E.f s'' ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ₂' (Limits.pullback.snd A.f s'') hφ₂' ≫ φ₂ = Limits.pullback.fst A.f s'' ≫ A.act ⟨_, hd⟩))),
          φ₂ = Limits.pullback.lift (Limits.pullback.fst E.f s'') (Limits.pullback.snd E.f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact Limits.pullback.condition) ≫ φ →
          φ₂' = Limits.pullback.lift (Limits.pullback.fst A.f s'') (Limits.pullback.snd A.f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact Limits.pullback.condition) ≫ φ' →
          (pt S'' s'' φ₂ hφ₂ φ₂' hφ₂' k₁ k₂ k₃).1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ φ' hφ' h₁ h₂ h₃).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πX),
        ∃ (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩))),
          pt S' s φ hφ φ' hφ' h₁ h₂ h₃ = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩)))
          (ψ : Limits.pullback E.f s ⟶ A.A) (hψ : ψ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (ψ' : Limits.pullback A.f s ⟶ E.A) (hψ' : ψ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (k₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ ψ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ ψ, by rw [Category.assoc, hψ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ ψ, by rw [Category.assoc, hψ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ ψ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ ψ', by rw [Category.assoc, hψ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ ψ', by rw [Category.assoc, hψ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ ψ = ψ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ ψ' = ψ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift ψ (Limits.pullback.snd E.f s) hψ ≫ ψ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift ψ' (Limits.pullback.snd A.f s) hψ' ≫ ψ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩))),
          pt S' s φ hφ φ' hφ' h₁ h₂ h₃ = pt S' s ψ hψ ψ' hψ' k₁ k₂ k₃ → φ = ψ ∧ φ' = ψ') ∧
      IsSeparated πX ∧ LocallyOfFiniteType πX ∧ LocallyOfFinitePresentation πX := by
  classical
  obtain ⟨D_EA, sepEA, lftEA, lfpEA⟩ := PairEq.exists_homRep S E.f A.f E.L A.L E.comm A.comm E.bundle A.bundle 𝓛E hE₁ hE₂ 𝓛A hA₁ hA₂
  obtain ⟨D_AE, sepAE, lftAE, lfpAE⟩ := PairEq.exists_homRep S A.f E.f A.L E.L A.comm E.comm A.bundle E.bundle 𝓛A hA₁ hA₂ 𝓛E hE₁ hE₂
  obtain ⟨D_EE, sepEE, lftEE, -⟩ := PairEq.exists_homRep S E.f E.f E.L E.L E.comm E.comm E.bundle E.bundle 𝓛E hE₁ hE₂ 𝓛E hE₁ hE₂
  obtain ⟨D_AA, sepAA, lftAA, -⟩ := PairEq.exists_homRep S A.f A.f A.L A.L A.comm A.comm A.bundle A.bundle 𝓛A hA₁ hA₂ 𝓛A hA₁ hA₂
  obtain ⟨P, πP, q₁, q₂, aE, bE, aA, bA, cE, kE, cA, kA, X, πX, m, hq₁, hq₂, hP,
      haE, hbE, haA, hbA, hcE, hkE, hcA, hkA, hm, hπX, hmE, hmA, hmdE, hmdA, hXuniv, hXsep, hXlft, hXlfp⟩ :=
    PairEq.exists_pairLocus_data r d S E A β D_EA D_AE D_EE D_AA sepEA lftEA lfpEA sepAE lftAE lfpAE sepEE lftEE sepAA lftAA
  refine ⟨X, πX, ?_⟩
  classical
  haveI := hm

  have ptc_EA : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (u v : pullback E.f s ⟶ A.A) (hu : u ≫ A.f = pullback.snd E.f s ≫ s) (hv : v ≫ A.f = pullback.snd E.f s ≫ s),
      u = v → D_EA.pt S' s u hu = D_EA.pt S' s v hv := by
    rintro S' _ s u v hu hv rfl; rfl
  have ptc_AE : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (u v : pullback A.f s ⟶ E.A) (hu : u ≫ E.f = pullback.snd A.f s ≫ s) (hv : v ≫ E.f = pullback.snd A.f s ≫ s),
      u = v → D_AE.pt S' s u hu = D_AE.pt S' s v hv := by
    rintro S' _ s u v hu hv rfl; rfl
  have ptc_EE : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (u v : pullback E.f s ⟶ E.A) (hu : u ≫ E.f = pullback.snd E.f s ≫ s) (hv : v ≫ E.f = pullback.snd E.f s ≫ s),
      u = v → D_EE.pt S' s u hu = D_EE.pt S' s v hv := by
    rintro S' _ s u v hu hv rfl; rfl
  have ptc_AA : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (u v : pullback A.f s ⟶ A.A) (hu : u ≫ A.f = pullback.snd A.f s ≫ s) (hv : v ≫ A.f = pullback.snd A.f s ≫ s),
      u = v → D_AA.pt S' s u hu = D_AA.pt S' s v hv := by
    rintro S' _ s u v hu hv rfl; rfl

  have uniq : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (z z' : SchemeHomOver s πX),
      z.1 ≫ m ≫ q₁ = z'.1 ≫ m ≫ q₁ → z.1 ≫ m ≫ q₂ = z'.1 ≫ m ≫ q₂ → z = z' := by
    intro S' _ s z z' e₁ e₂
    apply Subtype.ext
    rw [← cancel_mono m]
    refine (hP _ (z'.1 ≫ m ≫ q₁) (z'.1 ≫ m ≫ q₂) ?_).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · simp only [Category.assoc, hq₁, hq₂]
    · rw [Category.assoc]; exact e₁
    · rw [Category.assoc]; exact e₂
    · rw [Category.assoc]
    · rw [Category.assoc]

  have key : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ : pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = pullback.snd E.f s ≫ s)
      (φ' : pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = pullback.snd A.f s ≫ s)
      (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1))
      (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1))
      (h₃ : (∀ i : Fin (2 * 2), pullback.lift (pullback.fst E.f s ≫ E.act (β i)) (pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), pullback.lift (pullback.fst A.f s ≫ A.act (β i)) (pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              pullback.lift φ (pullback.snd E.f s) hφ ≫ φ' = pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              pullback.lift φ' (pullback.snd A.f s) hφ' ≫ φ = pullback.fst A.f s ≫ A.act ⟨_, hd⟩)),
      ∃ z : SchemeHomOver s πX, z.1 ≫ m ≫ q₁ = (D_EA.pt S' s φ hφ).1 ∧ z.1 ≫ m ≫ q₂ = (D_AE.pt S' s φ' hφ').1 := by
    intro S' _ s φ hφ φ' hφ' h₁ h₂ h₃
    obtain ⟨w, hw₁, hw₂⟩ := (hP (Spec (CommRingCat.of S')) (D_EA.pt S' s φ hφ).1 (D_AE.pt S' s φ' hφ').1
      (by rw [(D_EA.pt S' s φ hφ).2, (D_AE.pt S' s φ' hφ').2])).exists
    have hwP : w ≫ πP = s := by
      rw [← hq₁, ← Category.assoc, hw₁]; exact (D_EA.pt S' s φ hφ).2
    obtain ⟨g', hg'⟩ := hXuniv (Spec (CommRingCat.of S')) w
      (fun i => by
        have e1 : w ≫ aE i = _ := haE i S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        have e2 : w ≫ bE i = _ := hbE i S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        rw [e1, e2]
        exact congrArg Subtype.val (ptc_EA S' s _ _ _ _ (h₃.1 i)))
      (fun i => by
        have e1 : w ≫ aA i = _ := haA i S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        have e2 : w ≫ bA i = _ := hbA i S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        rw [e1, e2]
        exact congrArg Subtype.val (ptc_AE S' s _ _ _ _ (h₃.2.1 i)))
      (fun hd => by
        have e1 : w ≫ cE hd = _ := hcE hd S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        have e2 : w ≫ kE hd = _ := hkE hd S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        rw [e1, e2]
        exact congrArg Subtype.val (ptc_EE S' s _ _ _ _ (h₃.2.2 hd).1))
      (fun hd => by
        have e1 : w ≫ cA hd = _ := hcA hd S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        have e2 : w ≫ kA hd = _ := hkA hd S' s φ hφ φ' hφ' h₁ h₂ ⟨w, hwP⟩ hw₁ hw₂
        rw [e1, e2]
        exact congrArg Subtype.val (ptc_AA S' s _ _ _ _ (h₃.2.2 hd).2))
    refine ⟨⟨g', by rw [← hπX, ← Category.assoc, hg', hwP]⟩, ?_, ?_⟩
    · show g' ≫ m ≫ q₁ = _
      rw [← Category.assoc, hg', hw₁]
    · show g' ≫ m ≫ q₂ = _
      rw [← Category.assoc, hg', hw₂]
  choose pt hpt₁ hpt₂ using key
  refine ⟨pt, ?_, ?_, ?_, hXsep, hXlft, hXlfp⟩
  ·
    intro S' S'' _ _ ψ s s'' hs φ hφ φ' hφ' h₁ h₂ h₃ φ₂ hφ₂ φ₂' hφ₂' k₁ k₂ k₃ eφ eφ'
    have hz' : (Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ φ' hφ' h₁ h₂ h₃).1) ≫ πX = s'' := by
      rw [Category.assoc, (pt S' s φ hφ φ' hφ' h₁ h₂ h₃).2, hs]
    refine congrArg Subtype.val (uniq S'' s'' (pt S'' s'' φ₂ hφ₂ φ₂' hφ₂' k₁ k₂ k₃) ⟨_, hz'⟩ ?_ ?_)
    · show (pt S'' s'' φ₂ hφ₂ φ₂' hφ₂' k₁ k₂ k₃).1 ≫ m ≫ q₁ =
          (Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ φ' hφ' h₁ h₂ h₃).1) ≫ m ≫ q₁
      rw [hpt₁, Category.assoc, hpt₁, ← D_EA.nat S' S'' ψ s s'' hs φ hφ]
      exact congrArg Subtype.val (ptc_EA S'' s'' _ _ _ _ eφ)
    · show (pt S'' s'' φ₂ hφ₂ φ₂' hφ₂' k₁ k₂ k₃).1 ≫ m ≫ q₂ =
          (Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ φ' hφ' h₁ h₂ h₃).1) ≫ m ≫ q₂
      rw [hpt₂, Category.assoc, hpt₂, ← D_AE.nat S' S'' ψ s s'' hs φ' hφ']
      exact congrArg Subtype.val (ptc_AE S'' s'' _ _ _ _ eφ')
  ·
    intro S' _ s x
    have hx₁ : (x.1 ≫ m ≫ q₁) ≫ D_EA.πH = s := by
      rw [Category.assoc, Category.assoc, hq₁, hπX]; exact x.2
    have hx₂ : (x.1 ≫ m ≫ q₂) ≫ D_AE.πH = s := by
      rw [Category.assoc, Category.assoc, hq₂, hπX]; exact x.2
    obtain ⟨φ, hφ, h₁, hφpt⟩ := D_EA.surj S' s ⟨x.1 ≫ m ≫ q₁, hx₁⟩
    obtain ⟨φ', hφ', h₂, hφ'pt⟩ := D_AE.surj S' s ⟨x.1 ≫ m ≫ q₂, hx₂⟩
    have hwP : (x.1 ≫ m) ≫ πP = s := by
      rw [Category.assoc, hπX]; exact x.2
    have hw₁ : (x.1 ≫ m) ≫ q₁ = (D_EA.pt S' s φ hφ).1 := by
      rw [hφpt]; exact Category.assoc _ _ _
    have hw₂ : (x.1 ≫ m) ≫ q₂ = (D_AE.pt S' s φ' hφ').1 := by
      rw [hφ'pt]; exact Category.assoc _ _ _

    have homE_act : ∀ (x : ↥Λ) (κ : pullback E.f s ⟶ E.A) (hκ : κ ≫ E.f = pullback.snd E.f s ≫ s),
        κ = pullback.fst E.f s ≫ E.act x → (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ κ =
              (E.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩).1) :=
      fun x κ hκ e => PairEq.isHom_fst_comp_endo E.L (E.act x) (E.act_over x) (E.act_hom x) S' s κ hκ e
    have homA_act : ∀ (x : ↥Λ) (κ : pullback A.f s ⟶ A.A) (hκ : κ ≫ A.f = pullback.snd A.f s ≫ s),
        κ = pullback.fst A.f s ≫ A.act x → (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ κ =
              (A.L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ κ, by rw [Category.assoc, hκ, ← Category.assoc, pullback.lift_snd]⟩).1) :=
      fun x κ hκ e => PairEq.isHom_fst_comp_endo A.L (A.act x) (A.act_over x) (A.act_hom x) S' s κ hκ e
    have linE : (∀ i : Fin (2 * 2), pullback.lift (pullback.fst E.f s ≫ E.act (β i)) (pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact pullback.condition) ≫ φ = φ ≫ A.act (β i)) := by
      intro i
      have e1 : (x.1 ≫ m) ≫ aE i = _ := haE i S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
      have e2 : (x.1 ≫ m) ≫ bE i = _ := hbE i S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
      have e3 : (x.1 ≫ m) ≫ aE i = (x.1 ≫ m) ≫ bE i := by rw [Category.assoc, hmE i, ← Category.assoc]
      rw [e1, e2] at e3
      refine D_EA.inj S' s _ _ _ _ ?_ ?_ (Subtype.ext e3)
      · exact PairEq.isHom_liftComp E.L E.L A.L S' s _ (by rw [Category.assoc, E.act_over]; exact pullback.condition) φ hφ (homE_act (β i) _ (by rw [Category.assoc, E.act_over]; exact pullback.condition) rfl) h₁ _
          (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]) rfl
      · exact PairEq.isHom_liftComp E.L A.L A.L S' s φ hφ _ (by rw [Category.assoc, A.act_over]; exact pullback.condition) h₁ (homA_act (β i) _ (by rw [Category.assoc, A.act_over]; exact pullback.condition) rfl) _
          (by rw [Category.assoc, A.act_over, hφ]) (by rw [← Category.assoc, pullback.lift_fst])
    have linA : (∀ i : Fin (2 * 2), pullback.lift (pullback.fst A.f s ≫ A.act (β i)) (pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) := by
      intro i
      have e1 : (x.1 ≫ m) ≫ aA i = _ := haA i S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
      have e2 : (x.1 ≫ m) ≫ bA i = _ := hbA i S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
      have e3 : (x.1 ≫ m) ≫ aA i = (x.1 ≫ m) ≫ bA i := by rw [Category.assoc, hmA i, ← Category.assoc]
      rw [e1, e2] at e3
      refine D_AE.inj S' s _ _ _ _ ?_ ?_ (Subtype.ext e3)
      · exact PairEq.isHom_liftComp A.L A.L E.L S' s _ (by rw [Category.assoc, A.act_over]; exact pullback.condition) φ' hφ' (homA_act (β i) _ (by rw [Category.assoc, A.act_over]; exact pullback.condition) rfl) h₂ _
          (by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]) rfl
      · exact PairEq.isHom_liftComp A.L E.L E.L S' s φ' hφ' _ (by rw [Category.assoc, E.act_over]; exact pullback.condition) h₂ (homE_act (β i) _ (by rw [Category.assoc, E.act_over]; exact pullback.condition) rfl) _
          (by rw [Category.assoc, E.act_over, hφ']) (by rw [← Category.assoc, pullback.lift_fst])
    have deg : (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              pullback.lift φ (pullback.snd E.f s) hφ ≫ φ' = pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              pullback.lift φ' (pullback.snd A.f s) hφ' ≫ φ = pullback.fst A.f s ≫ A.act ⟨_, hd⟩) := by
      intro hd
      constructor
      · have e1 : (x.1 ≫ m) ≫ cE hd = _ := hcE hd S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
        have e2 : (x.1 ≫ m) ≫ kE hd = _ := hkE hd S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
        have e3 : (x.1 ≫ m) ≫ cE hd = (x.1 ≫ m) ≫ kE hd := by rw [Category.assoc, hmdE hd, ← Category.assoc]
        rw [e1, e2] at e3
        refine D_EE.inj S' s _ _ _ _ ?_ ?_ (Subtype.ext e3)
        · exact PairEq.isHom_liftComp E.L A.L E.L S' s φ hφ φ' hφ' h₁ h₂ _
            (by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]) rfl
        · exact homE_act ⟨_, hd⟩ _ (by rw [Category.assoc, E.act_over]; exact pullback.condition) rfl
      · have e1 : (x.1 ≫ m) ≫ cA hd = _ := hcA hd S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
        have e2 : (x.1 ≫ m) ≫ kA hd = _ := hkA hd S' s φ hφ φ' hφ' h₁ h₂ ⟨x.1 ≫ m, hwP⟩ hw₁ hw₂
        have e3 : (x.1 ≫ m) ≫ cA hd = (x.1 ≫ m) ≫ kA hd := by rw [Category.assoc, hmdA hd, ← Category.assoc]
        rw [e1, e2] at e3
        refine D_AA.inj S' s _ _ _ _ ?_ ?_ (Subtype.ext e3)
        · exact PairEq.isHom_liftComp A.L E.L A.L S' s φ' hφ' φ hφ h₂ h₁ _
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]) rfl
        · exact homA_act ⟨_, hd⟩ _ (by rw [Category.assoc, A.act_over]; exact pullback.condition) rfl
    refine ⟨φ, hφ, φ', hφ', h₁, h₂, ⟨linE, linA, deg⟩, ?_⟩
    apply uniq S' s
    · rw [hpt₁, hφpt]
    · rw [hpt₂, hφ'pt]
  ·
    intro S' _ s φ hφ φ' hφ' h₁ h₂ h₃ ψ hψ ψ' hψ' k₁ k₂ k₃ e
    refine ⟨D_EA.inj S' s φ ψ hφ hψ h₁ k₁ (Subtype.ext ?_), D_AE.inj S' s φ' ψ' hφ' hψ' h₂ k₂ (Subtype.ext ?_)⟩
    · rw [← hpt₁ S' s φ hφ φ' hφ' h₁ h₂ h₃, ← hpt₁ S' s ψ hψ ψ' hψ' k₁ k₂ k₃, e]
    · rw [← hpt₂ S' s φ hφ φ' hφ' h₁ h₂ h₃, ← hpt₂ S' s ψ hψ ψ' hψ' k₁ k₂ k₃, e]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_represents_homPair_act_comp_eq_of_closedImmersionBySections
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_represents_homPair_act_comp_eq_of_closedImmersionBySections (solution)
