-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/eb544ede-0f75-5baf-8464-0e145a565b2f

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_schemeKerStr_and_schemeNsmul_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I"
p2m_attr_erase "instance" "DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace Ws23KP

theorem mul_coe_congr {S : Type} [CommRing S] {A Z : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {b₁ b₂ : Z ⟶ Spec (CommRingCat.of S)} (hb : b₁ = b₂)
    (P Q : SchemeHomOver b₁ f) (P' Q' : SchemeHomOver b₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul b₁ P Q).1 = (L.mul b₂ P' Q').1 := by
  subst hb
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'; obtain ⟨q, hq⟩ := Q; obtain ⟨q', hq'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem locIso_of_iso {S' : Type} [CommRing S'] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase p M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

def pullbackInvIso {X Y : Scheme.{0}} (ρ : X ⟶ Y) [IsIso ρ] (M : Y.Modules) :
    (Scheme.Modules.pullback (inv ρ)).obj ((Scheme.Modules.pullback ρ).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp (inv ρ) ρ).app M ≪≫ (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id ρ)).app M ≪≫
    (Scheme.Modules.pullbackId Y).app M

theorem specMap_id (R'' : Type) [CommRing R''] :
    Spec.map (CommRingCat.ofHom (RingHom.id R'')) = 𝟙 (Spec (CommRingCat.of R'')) := by
  rw [CommRingCat.ofHom_id]
  exact Scheme.Spec.map_id _

theorem isPullback_of_isIso_specMap_id {R'' : Type} [CommRing R''] {X Y : Scheme.{0}} (ρ : X ⟶ Y) [IsIso ρ]
    (p : X ⟶ Spec (CommRingCat.of R'')) (q : Y ⟶ Spec (CommRingCat.of R'')) (h : ρ ≫ q = p) :
    IsPullback ρ p q (Spec.map (CommRingCat.ofHom (RingHom.id R''))) := by
  rw [specMap_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [h, Category.comp_id]⟩

section Square

variable {S R R' : Type} [CommRing S] [CommRing R] [CommRing R']
  {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (σ' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
  (φ : R →+* R') (hπ : Spec.map (CommRingCat.ofHom φ) ≫ σ = σ')
  (j : pullback f σ' ⟶ pullback f σ)
  (hj₁ : j ≫ pullback.fst f σ = pullback.fst f σ')
  (hj₂ : j ≫ pullback.snd f σ = pullback.snd f σ' ≫ Spec.map (CommRingCat.ofHom φ))
  (L' : RelativeGroupLaw R (pullback.snd f σ))
  (hL' : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.snd f σ)),
      (L'.mul t P Q).1 ≫ pullback.fst f σ =
        (L.mul (t ≫ σ)
          ⟨P.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
  (Lk : RelativeGroupLaw R' (pullback.snd f σ'))
  (hLk : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')),
      (Lk.mul t P Q).1 ≫ pullback.fst f σ' =
        (L.mul (t ≫ σ')
          ⟨P.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)

include hπ hj₁ hj₂ in
theorem isPullback_j : IsPullback j (pullback.snd f σ') (pullback.snd f σ) (Spec.map (CommRingCat.ofHom φ)) := by
  have big : IsPullback (j ≫ pullback.fst f σ) (pullback.snd f σ') f (Spec.map (CommRingCat.ofHom φ) ≫ σ) := by
    rw [hj₁, hπ]
    exact IsPullback.of_hasPullback f σ'
  exact IsPullback.of_right big hj₂ (IsPullback.of_hasPullback f σ)

def pushPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (y : SchemeHomOver t (pullback.snd f σ')) :
    SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ) :=
  ⟨y.1 ≫ j, by rw [Category.assoc, hj₂, ← Category.assoc, y.2]⟩

@[scoped simp] theorem pushPt_coe {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (y : SchemeHomOver t (pullback.snd f σ')) :
    (pushPt σ σ' φ j hj₂ y).1 = y.1 ≫ j := rfl

include hπ hj₁ in

def liftPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) :
    SchemeHomOver t (pullback.snd f σ') :=
  ⟨(isPullback_j σ σ' φ hπ j hj₁ hj₂).lift x.1 t x.2, IsPullback.lift_snd _ _ _ _⟩

include hπ hj₁ in
theorem liftPt_comp_j {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) :
    (liftPt σ σ' φ hπ j hj₁ hj₂ x).1 ≫ j = x.1 :=
  IsPullback.lift_fst _ _ _ _

include hπ hj₁ in
theorem pushPt_liftPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) :
    pushPt σ σ' φ j hj₂ (liftPt σ σ' φ hπ j hj₁ hj₂ x) = x :=
  Subtype.ext (liftPt_comp_j σ σ' φ hπ j hj₁ hj₂ x)

include hπ hj₁ in

theorem pushPt_injective {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} :
    Function.Injective (pushPt σ σ' φ j hj₂ (t := t)) := by
  intro y y' h
  have h1 : y.1 ≫ j = y'.1 ≫ j := congrArg Subtype.val h
  apply Subtype.ext
  exact (isPullback_j σ σ' φ hπ j hj₁ hj₂).hom_ext h1 (by rw [y.2, y'.2])

include hπ hj₁ in
theorem liftPt_pushPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (y : SchemeHomOver t (pullback.snd f σ')) :
    liftPt σ σ' φ hπ j hj₁ hj₂ (pushPt σ σ' φ j hj₂ y) = y :=
  pushPt_injective σ σ' φ hπ j hj₁ hj₂ (pushPt_liftPt σ σ' φ hπ j hj₁ hj₂ _)

include hπ hj₁ hj₂ hL' hLk in
theorem mul_comp_j {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')) :
    (Lk.mul t P Q).1 ≫ j =
      (L'.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ j, by rw [Category.assoc, hj₂, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ j, by rw [Category.assoc, hj₂, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, hj₁, hLk T t P Q, hL' T _ _ _]
    exact mul_coe_congr L (by rw [Category.assoc, hπ]) _ _ _ _
      (by show P.1 ≫ pullback.fst f σ' = (P.1 ≫ j) ≫ pullback.fst f σ; rw [Category.assoc, hj₁])
      (by show Q.1 ≫ pullback.fst f σ' = (Q.1 ≫ j) ≫ pullback.fst f σ; rw [Category.assoc, hj₁])
  · trans t ≫ Spec.map (CommRingCat.ofHom φ)
    · rw [Category.assoc, hj₂, ← Category.assoc, (Lk.mul t P Q).2]
    · exact ((L'.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) _ _).2).symm

include hπ hj₁ hj₂ hL' hLk in

theorem pushPt_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')) :
    pushPt σ σ' φ j hj₂ (Lk.mul t P Q) = L'.mul _ (pushPt σ σ' φ j hj₂ P) (pushPt σ σ' φ j hj₂ Q) :=
  Subtype.ext (mul_comp_j L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t P Q)

include hπ hj₁ hj₂ hL' hLk in
theorem pushPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) :
    pushPt σ σ' φ j hj₂ (Lk.one t) = L'.one _ := by
  letI : Group (SchemeHomOver t (pullback.snd f σ')) := Lk.pointGroup t
  letI : Group (SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ)) := L'.pointGroup _
  let ψ : SchemeHomOver t (pullback.snd f σ') →* SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f σ) :=
    MonoidHom.mk' (pushPt σ σ' φ j hj₂) (pushPt_mul L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t)
  exact map_one ψ

include hπ hj₁ hj₂ hL' hLk in
theorem one_comp_j {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (Lk.one t).1 ≫ j = (L'.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 :=
  congrArg Subtype.val (pushPt_one L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t)

include hπ hj₁ hj₂ hL' hLk in
theorem eq_one_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (y : SchemeHomOver t (pullback.snd f σ')) :
    pushPt σ σ' φ j hj₂ y = L'.one _ ↔ y = Lk.one t := by
  rw [← pushPt_one L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t]
  exact (pushPt_injective σ σ' φ hπ j hj₁ hj₂).eq_iff

include hπ hj₁ hj₂ hL' hLk in
theorem mul_self_eq_one_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (y : SchemeHomOver t (pullback.snd f σ')) :
    L'.mul _ (pushPt σ σ' φ j hj₂ y) (pushPt σ σ' φ j hj₂ y) = L'.one _ ↔ Lk.mul t y y = Lk.one t := by
  rw [← pushPt_mul L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk, ← pushPt_one L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t]
  exact (pushPt_injective σ σ' φ hπ j hj₁ hj₂).eq_iff

include hπ hj₁ hj₂ hL' hLk in
theorem locIso_sliceAt_iff (𝓜 : (pullback f σ).Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    {R'' : Type} [CommRing R''] (t : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    (y : SchemeHomOver t (pullback.snd f σ')) :
    LocIsoOnBase (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).obj
          (mumfordBundle (pullback.snd f σ) L' 𝓜))
        (𝟙_ ((pullback (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ))).Modules)) ↔
      LocIsoOnBase (pullback.snd (pullback.snd f σ') t)
        ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ') y)).obj
          (mumfordBundle (pullback.snd f σ') Lk ((Scheme.Modules.pullback j).obj 𝓜)))
        (𝟙_ ((pullback (pullback.snd f σ') t).Modules)) := by
  have hsq := isPullback_j σ σ' φ hπ j hj₁ hj₂

  obtain ⟨eΛ⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
    R R' φ (pullback.snd f σ) L' (pullback.snd f σ') Lk j hsq
    (fun t' P Q => mul_comp_j L σ σ' φ hπ j hj₁ hj₂ L' hL' Lk hLk t' P Q) 𝓜 h𝓜

  have big : IsPullback (pullback.fst (pullback.snd f σ') t ≫ j) (pullback.snd (pullback.snd f σ') t)
      (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd f σ') t) hsq
  let ρ : pullback (pullback.snd f σ') t ⟶ pullback (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)) :=
    big.isoPullback.hom
  have hρ₁ : ρ ≫ pullback.fst _ _ = pullback.fst (pullback.snd f σ') t ≫ j := big.isoPullback_hom_fst
  have hρ₂ : ρ ≫ pullback.snd _ _ = pullback.snd (pullback.snd f σ') t := big.isoPullback_hom_snd
  haveI : IsIso ρ := inferInstance
  have hρ : IsPullback ρ (pullback.snd (pullback.snd f σ') t) (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom (RingHom.id R''))) :=
    isPullback_of_isIso_specMap_id ρ _ _ hρ₂
  have hρ' : IsPullback (inv ρ) (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ))) (pullback.snd (pullback.snd f σ') t)
      (Spec.map (CommRingCat.ofHom (RingHom.id R''))) :=
    isPullback_of_isIso_specMap_id (inv ρ) _ _ (by rw [IsIso.inv_comp_eq, hρ₂])

  have hslice : sliceAt (pullback.snd f σ') y ≫
      pullback.lift (pullback.fst (pullback.snd f σ') (pullback.snd f σ') ≫ j) (pullback.snd (pullback.snd f σ') (pullback.snd f σ') ≫ j)
        (by rw [Category.assoc, Category.assoc, hsq.w, ← Category.assoc, pullback.condition, Category.assoc]) =
      ρ ≫ sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y) := by
    apply pullback.hom_ext
    · simp only [sliceAt, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
      exact hρ₁.symm
    · simp only [sliceAt, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, pushPt_coe]
      rw [reassoc_of% hρ₂]

  have eA : (Scheme.Modules.pullback (sliceAt (pullback.snd f σ') y)).obj
        (mumfordBundle (pullback.snd f σ') Lk ((Scheme.Modules.pullback j).obj 𝓜)) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).obj
        (mumfordBundle (pullback.snd f σ) L' 𝓜)) :=
    (Scheme.Modules.pullback (sliceAt (pullback.snd f σ') y)).mapIso eΛ ≪≫
      (Scheme.Modules.pullbackComp (sliceAt (pullback.snd f σ') y) _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hslice).app _ ≪≫
      ((Scheme.Modules.pullbackComp ρ (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).app _).symm
  have eU : (Scheme.Modules.pullback ρ).obj (𝟙_ ((pullback (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ))).Modules)) ≅
      𝟙_ ((pullback (pullback.snd f σ') t).Modules) :=
    Scheme.Modules.pullbackUnitIso ρ
  have E₁ := LocIsoOnBase.equivalence (pullback.snd (pullback.snd f σ') t)
  have E₂ := LocIsoOnBase.equivalence (pullback.snd (pullback.snd f σ) (t ≫ Spec.map (CommRingCat.ofHom φ)))
  constructor
  · intro h
    have h' := LocIsoOnBase.pullback_of_isPullback (RingHom.id R'') hρ h
    exact E₁.trans (locIso_of_iso _ eA) (E₁.trans h' (locIso_of_iso _ eU))
  · intro h
    have h1 : LocIsoOnBase (pullback.snd (pullback.snd f σ') t)
        ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (sliceAt (pullback.snd f σ) (pushPt σ σ' φ j hj₂ y))).obj
          (mumfordBundle (pullback.snd f σ) L' 𝓜)))
        ((Scheme.Modules.pullback ρ).obj (𝟙_ _)) :=
      E₁.trans (locIso_of_iso _ eA.symm) (E₁.trans h (locIso_of_iso _ eU.symm))
    have h2 := LocIsoOnBase.pullback_of_isPullback (RingHom.id R'') hρ' h1
    exact E₂.trans (locIso_of_iso _ (pullbackInvIso ρ _).symm) (E₂.trans h2 (locIso_of_iso _ (pullbackInvIso ρ _)))

omit φ hπ j hj₁ hj₂ Lk hLk in
theorem bundle_snd (hA : AbelianSchemePropertyBundle S f) : AbelianSchemePropertyBundle R (pullback.snd f σ) :=
  hA.of_isPullback (IsPullback.of_hasPullback f σ)

include hL' in
theorem isCommutative_of_compat (hc : L.IsCommutative) : L'.IsCommutative := by
  intro T t x y
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [hL' T t x y, hL' T t y x, hc.mul_comm]
  · rw [(L'.mul t x y).2, (L'.mul t y x).2]

omit Lk hLk in

theorem compat_baseChange (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t (pullback.snd f σ')) :
    ((L.baseChange σ').mul t P Q).1 ≫ pullback.fst f σ' =
      (L.mul (t ≫ σ')
        ⟨P.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f σ', by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 :=
  congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul σ' L t P Q)

end Square

end Ws23KP
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening.Ws23KP"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening.Ws23KP"

namespace Ws23KPAsm

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem one_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id _)
  rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]

theorem nsmul_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    (L.nsmul t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have hid : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint) = P :=
    Subtype.ext (Category.comp_id _)
  have hn := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  rw [hid] at hn
  rw [← hn, GoodReductionJacobian.schemeHomOverComp_coe]
  rfl

theorem exists_comp_kerFst_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (∃ ψ₂ : T ⟶ L.schemeKer 2, ψ₂ ≫ pullback.fst (L.schemeNsmul 2) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = x.1) ↔
      L.mul t x x = L.one t := by
  have h2 : L.mul t x x = L.nsmul t 2 x := by
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_zero, L.one_mul]
  constructor
  · rintro ⟨ψ₂, hψ₂⟩
    rw [h2]
    apply Subtype.ext
    rw [nsmul_coe, one_coe, ← hψ₂, Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    calc ψ₂ ≫ pullback.snd (L.schemeNsmul 2) (L.one (𝟙 (Spec (CommRingCat.of R)))).1
        = ψ₂ ≫ pullback.snd (L.schemeNsmul 2) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
            ((L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
          rw [(L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]
      _ = ψ₂ ≫ (pullback.fst (L.schemeNsmul 2) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ L.schemeNsmul 2) ≫ f := by
          rw [← Category.assoc (pullback.snd _ _), ← pullback.condition]
      _ = (ψ₂ ≫ pullback.fst (L.schemeNsmul 2) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by
          simp only [Category.assoc, L.schemeNsmul_over]
      _ = t := by rw [hψ₂, x.2]
  · intro hx
    rw [h2] at hx
    have h1 : x.1 ≫ L.schemeNsmul 2 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
      rw [← nsmul_coe, hx, one_coe]
    exact ⟨pullback.lift x.1 t h1, pullback.lift_fst _ _ _⟩

end Ws23KPAsm
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening.Ws23KP"

open Ws23KP Ws23KPAsm in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R]
    (j : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (L' : RelativeGroupLaw R (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))))
    (hL' : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
            (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛₀ 𝓛 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules)
    (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hk : ∀ (k : ℕ) (Lk : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))),
            (Lk.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk ((Scheme.Modules.pullback (j k)).obj 𝓛₀) ∧
        KernelIsTwoTorsion (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))) Lk ((Scheme.Modules.pullback (j k)).obj 𝓛)) :
    KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛₀ ∧
    KernelIsTwoTorsion (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛 := by
  classical

  let σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let fR := pullback.snd E.f σ
  let σk : ∀ k : ℕ, Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))) ⟶ Spec (CommRingCat.of S) :=
    fun k => Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
  let φk : ∀ k : ℕ, R →+* R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1) := fun k => Ideal.Quotient.mk _
  have hπ : ∀ k, Spec.map (CommRingCat.ofHom (φk k)) ≫ σ = σk k := by
    intro k
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let Lk : ∀ k, RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) (pullback.snd E.f (σk k)) :=
    fun k => E.L.baseChange (σk k)
  have hLk := fun k => compat_baseChange E.L (σk k)
  have hkk := fun k => hk k (Lk k) (hLk k)

  have hAR : AbelianSchemePropertyBundle R fR := bundle_snd σ E.bundle
  haveI : IsProper fR := hAR.proper
  have hc' : L'.IsCommutative := isCommutative_of_compat E.L σ L' hL' E.comm

  let eR : Spec (CommRingCat.of R) ⟶ pullback E.f σ := (L'.one (𝟙 (Spec (CommRingCat.of R)))).1
  have heR : eR ≫ fR = 𝟙 _ := (L'.one (𝟙 _)).2
  haveI : IsClosedImmersion eR := by
    have : IsClosedImmersion (eR ≫ fR) := by rw [heR]; infer_instance
    exact IsClosedImmersion.of_comp eR fR

  obtain ⟨K, ιK, hKcl, hKpts⟩ :=
    AbelianSchemePropertyBundle.exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
      hAR L' 𝓛₀ h𝓛₀
  haveI := hKcl
  have hfin_e : ((eR ≫ fR).base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite := by
    rw [heR]
    exact (Set.finite_singleton _).preimage (fun _ _ _ _ h => by simpa using h)
  have habs₁ := AlgebraicGeometry.exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper fR ιK eR hfin_e ?_
  swap
  ·
    intro k R'' _ ψ ht
    obtain ⟨t, ht⟩ := ht
    let x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (φk k))) fR := ⟨ψ, ht.symm⟩
    let y := liftPt σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) x
    have hxy : pushPt σ (σk k) (φk k) (j k) (hj₂ k) y = x := pushPt_liftPt σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) x
    have e0 : (∃ ψ₁ : Spec (CommRingCat.of R'') ⟶ K, ψ₁ ≫ ιK = ψ) ↔ _ := hKpts R'' _ x
    have e1 := locIso_sliceAt_iff E.L σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) L' hL' (Lk k) (hLk k) 𝓛₀ h𝓛₀ t y
    rw [hxy] at e1
    have e2 : _ ↔ y = (Lk k).one t :=
      ⟨(hkk k).1 R'' t y, fun hy => by
        rw [hy]
        exact (isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing _ _ (Lk k) _
          (Scheme.Modules.IsInvertible.pullback (j k) h𝓛₀) R'' t _).mp ((Lk k).isInStabilizer_one _ t)⟩
    have e3 := eq_one_iff E.L σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) L' hL' (Lk k) (hLk k) t y
    rw [hxy] at e3
    have e4 : x = L'.one _ ↔ (∃ ψ₂ : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R), ψ₂ ≫ eR = ψ) := by
      constructor
      · intro hx1
        refine ⟨t ≫ Spec.map (CommRingCat.ofHom (φk k)), ?_⟩
        rw [← one_coe L']
        exact (congrArg Subtype.val hx1).symm
      · rintro ⟨ψ₂, hψ₂⟩
        apply Subtype.ext
        have hψ₂' : ψ₂ = t ≫ Spec.map (CommRingCat.ofHom (φk k)) := by
          rw [ht, ← hψ₂, Category.assoc, heR, Category.comp_id]
        show ψ = _
        rw [one_coe L', ← hψ₂, hψ₂']
    exact e0.trans (e1.trans (e2.trans (e3.symm.trans e4)))

  obtain ⟨K₂, ιK₂, hK₂cl, hK₂pts⟩ :=
    AbelianSchemePropertyBundle.exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
      hAR L' 𝓛 h𝓛
  haveI := hK₂cl
  let ι' := pullback.fst (L'.schemeNsmul 2) eR
  haveI : IsClosedImmersion ι' := inferInstance
  have hfin₂ : ((ι' ≫ fR).base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite := by
    haveI : Smooth E.f := E.bundle.smooth
    haveI : SmoothOfRelativeDimension 2 E.f :=
      GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq E.L 2 E.dim_fibre
    haveI : SmoothOfRelativeDimension 2 fR := by
      haveI := @smoothOfRelativeDimension_isStableUnderBaseChange 2
      exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 2) E.f σ inferInstance
    obtain ⟨hfinK, -⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.isFinite_flat_schemeKerStr_and_schemeNsmul_of_abelianSchemePropertyBundle
        L' hc' hAR 2 2 two_ne_zero
    have hNf : L'.schemeNsmul 2 ≫ fR = fR := L'.schemeNsmul_over 2
    have heq : ι' ≫ fR = L'.schemeKerStr 2 := by
      change pullback.fst (L'.schemeNsmul 2) eR ≫ fR = pullback.snd (L'.schemeNsmul 2) eR
      calc pullback.fst (L'.schemeNsmul 2) eR ≫ fR
          = pullback.fst (L'.schemeNsmul 2) eR ≫ L'.schemeNsmul 2 ≫ fR := by rw [hNf]
        _ = (pullback.snd (L'.schemeNsmul 2) eR ≫ eR) ≫ fR := by rw [← Category.assoc, pullback.condition]
        _ = pullback.snd (L'.schemeNsmul 2) eR := by rw [Category.assoc, heR, Category.comp_id]
    rw [heq]
    haveI := hfinK
    exact (L'.schemeKerStr 2).finite_preimage_singleton _
  have habs₂ := AlgebraicGeometry.exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper fR ιK₂ ι' hfin₂ ?_
  swap
  · intro k R'' _ ψ ht
    obtain ⟨t, ht⟩ := ht
    let x : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (φk k))) fR := ⟨ψ, ht.symm⟩
    let y := liftPt σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) x
    have hxy : pushPt σ (σk k) (φk k) (j k) (hj₂ k) y = x := pushPt_liftPt σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) x
    have e0 : (∃ ψ₁ : Spec (CommRingCat.of R'') ⟶ K₂, ψ₁ ≫ ιK₂ = ψ) ↔ _ := hK₂pts R'' _ x
    have e1 := locIso_sliceAt_iff E.L σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) L' hL' (Lk k) (hLk k) 𝓛 h𝓛 t y
    rw [hxy] at e1
    have e2 := (hkk k).2 R'' t y
    have e3 := mul_self_eq_one_iff E.L σ (σk k) (φk k) (hπ k) (j k) (hj₁ k) (hj₂ k) L' hL' (Lk k) (hLk k) t y
    rw [hxy] at e3
    have e4 : L'.mul _ x x = L'.one _ ↔ (∃ ψ₂ : Spec (CommRingCat.of R'') ⟶ L'.schemeKer 2, ψ₂ ≫ ι' = ψ) :=
      (exists_comp_kerFst_iff L' _ x).symm
    exact e0.trans (e1.trans (e2.trans (e3.symm.trans e4)))

  refine ⟨?_, ?_⟩
  · intro R' _ t' x' hx'
    obtain ⟨ψ₂, hψ₂⟩ := (habs₁ R' x'.1).mp ((hKpts R' t' x').mpr hx')
    apply Subtype.ext
    have hψ₂' : ψ₂ = t' := by
      rw [← x'.2, ← hψ₂, Category.assoc, heR, Category.comp_id]
    rw [one_coe L', ← hψ₂, hψ₂']
  · intro R' _ t' x'
    exact (hK₂pts R' t' x').symm.trans ((habs₂ R' x'.1).trans (exists_comp_kerFst_iff L' t' x'))

end S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_and_kernelIsTwoTorsion_of_forall_thickening (solution)
