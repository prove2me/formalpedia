-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/906a5535-77ba-5bcc-9e5c-49ef776ca5a7

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

import Theorems.Thm_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_and_trace_restrict_eq_of_charP_of_isIndefiniteRamifiedExactlyAt_of_isUnit
import Theorems.Thm_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP
p2m_attr_erase "instance" "PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply"
p2m_attr_erase "simp" "CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM IsLocalRing AlgebraicGeometry.Polarisation AlgebraicGeometry.SmallExtension

open scoped Quaternion TensorProduct

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (hqq : IsUnit ((q * q' : ℕ) : k))
    (E : FakeEllipticCurve Λ N k) (𝒦 : E.A.OrderedAffineCover)

    (H : Type) [AddCommGroup H] [Module k H] (A₁ : Submodule k H)
    (cls : ↥(LinearMap.ker ((OModulePresheaf.unit E.f).d 𝒦 1)) →ₗ[k] H)
    (hrange : LinearMap.range cls = A₁)
    (hker : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit E.f).d 𝒦 1)),
      cls z = 0 ↔ (z : (OModulePresheaf.unit E.f).cochain 𝒦 1) ∈ LinearMap.range ((OModulePresheaf.unit E.f).d 𝒦 0))
    (Φ : ↥Λ → (H →ₗ[k] H))
    (hΦA : ∀ (x : ↥Λ), ∀ h ∈ A₁, Φ x h ∈ A₁)
    (hΦ_add : ∀ (x y : ↥Λ), ∀ h ∈ A₁, Φ (x + y) h = Φ x h + Φ y h)
    (hΦ_one : ∀ (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ), ∀ h ∈ A₁, Φ ⟨1, h1⟩ h = h)
    (hΦ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), ∀ h ∈ A₁,
      Φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ h = Φ y (Φ x h))

    (hΦ : ∀ (x : ↥Λ) (𝒲 : E.A.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
        (hlam : ∀ w, 𝒲.U w ≤ E.act x ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ (𝟙 E.A) ⁻¹ᵁ 𝒦.U (lam' w))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit E.f).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := E.f) (E.act x) 𝒲 𝒦 lam hlam 1 z.1 -
            OModulePresheaf.unitPullback (πX := E.f) (𝟙 E.A) 𝒲 𝒦 lam' hlam' 1 z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit E.f).d 𝒲 0) →
        Φ x (cls z) = cls z')

    (hμns : ¬ ∃ c₀ : k, ∀ h ∈ A₁, Φ μ h = c₀ • h)

    (t : H ⊗[k] H) (a₁ a₂ : H) (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₁) (c : k)
    (ht : t = c • (a₁ ⊗ₜ[k] a₂ - a₂ ⊗ₜ[k] a₁))
    (hbal : ∀ x : ↥Λ,
      TensorProduct.map LinearMap.id (Φ x) t = TensorProduct.map (Φ (star x)) LinearMap.id t) :
    t = 0 := by
  classical

  obtain ⟨hdim, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.finrank_eq_two_and_trace_restrict_eq_of_charP_of_isIndefiniteRamifiedExactlyAt_of_isUnit hqq' hB Λ hΛ μ hμ star hstar k hqq E 𝒦 H A₁ cls hrange hker Φ hΦA hΦ_add hΦ_one hΦ_mul hΦ
  haveI : Module.Finite k ↥A₁ := Module.finite_of_finrank_eq_succ hdim

  obtain ⟨Ψ, hΨ_apply⟩ : ∃ Ψ : ↥Λ → (Module.Dual k ↥A₁ →ₗ[k] Module.Dual k ↥A₁),
      ∀ (x : ↥Λ) (φ : Module.Dual k ↥A₁) (h : ↥A₁), Ψ x φ h = φ ⟨Φ x h, hΦA x h h.2⟩ :=
    ⟨fun x => ((Φ x).restrict (hΦA x)).dualMap, fun x φ h => rfl⟩
  have hW : Module.finrank k (Module.Dual k ↥A₁) = 2 := by rw [Subspace.dual_finrank_eq, hdim]
  have hΨ_add : ∀ x y : ↥Λ, Ψ (x + y) = Ψ x + Ψ y := by
    intro x y; apply LinearMap.ext; intro φ; apply LinearMap.ext; intro h
    rw [LinearMap.add_apply, LinearMap.add_apply, hΨ_apply, hΨ_apply, hΨ_apply, ← map_add]
    congr 1; apply Subtype.ext; simp only [Submodule.coe_add]; exact hΦ_add x y h h.2
  have hΨ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Ψ ⟨1, h1⟩ = LinearMap.id := by
    intro h1; apply LinearMap.ext; intro φ; apply LinearMap.ext; intro h
    rw [hΨ_apply, LinearMap.id_apply]; congr 1; apply Subtype.ext; exact hΦ_one h1 h h.2
  have hΨ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      Ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = Ψ x ∘ₗ Ψ y := by
    intro x y hxy; apply LinearMap.ext; intro φ; apply LinearMap.ext; intro h
    rw [LinearMap.comp_apply, hΨ_apply, hΨ_apply, hΨ_apply]; congr 1; apply Subtype.ext; exact hΦ_mul x y hxy h h.2

  obtain ⟨θ, e, he, hθadd, hθone, hθmul, hspan, hθstar, hθtr, hθdet, -⟩ :=
    CerednikDrinfeld.SpecialModule.exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit hqq' hB Λ hΛ μ hμ star hstar k hqq
      (Module.Dual k ↥A₁) hW Ψ hΨ_add hΨ_one hΨ_mul
  have hMdet : (θ μ).det ≠ 0 := by rw [hθdet]; exact hqq.ne_zero
  have he' : ∀ (x : ↥Λ) (v : Fin 2 → k), e.symm ((θ x).mulVec v) = Ψ x (e.symm v) := by
    intro x v; apply e.injective; rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

  obtain ⟨B, hBap⟩ : ∃ B : Module.Dual k ↥A₁ →ₗ[k] Module.Dual k ↥A₁ →ₗ[k] k,
      ∀ φ ψ, B φ ψ = c * (φ ⟨a₁, ha₁⟩ * ψ ⟨a₂, ha₂⟩ - φ ⟨a₂, ha₂⟩ * ψ ⟨a₁, ha₁⟩) :=
    ⟨LinearMap.mk₂ k (fun φ ψ => c * (φ ⟨a₁, ha₁⟩ * ψ ⟨a₂, ha₂⟩ - φ ⟨a₂, ha₂⟩ * ψ ⟨a₁, ha₁⟩))
      (fun _ _ _ => by simp only [LinearMap.add_apply]; ring)
      (fun _ _ _ => by simp only [LinearMap.smul_apply, smul_eq_mul]; ring)
      (fun _ _ _ => by simp only [LinearMap.add_apply]; ring)
      (fun _ _ _ => by simp only [LinearMap.smul_apply, smul_eq_mul]; ring), fun _ _ => rfl⟩

  have hBbal : ∀ (y : ↥Λ) (φ ψ : Module.Dual k ↥A₁), B (Ψ (star y) φ) ψ = B φ (Ψ y ψ) := by
    intro y φ ψ
    have h := congrArg (LinearMap.mul' k k ∘ₗ TensorProduct.map (Subspace.dualLift A₁ φ) (Subspace.dualLift A₁ ψ)) (hbal y)
    rw [ht] at h
    simp only [map_smul, map_sub, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      LinearMap.id_apply, smul_eq_mul] at h
    simp only [Subspace.dualLift_of_mem ha₁, Subspace.dualLift_of_mem ha₂, Subspace.dualLift_of_mem (hΦA y a₁ ha₁),
      Subspace.dualLift_of_mem (hΦA y a₂ ha₂), Subspace.dualLift_of_mem (hΦA (star y) a₁ ha₁),
      Subspace.dualLift_of_mem (hΦA (star y) a₂ ha₂)] at h
    rw [hBap, hBap, hΨ_apply, hΨ_apply, hΨ_apply, hΨ_apply]
    exact h.symm

  obtain ⟨β, hβ⟩ : ∃ β : (Fin 2 → k) →ₗ[k] (Fin 2 → k) →ₗ[k] k, ∀ w₁ w₂, β w₁ w₂ = B (e.symm w₁) (e.symm w₂) :=
    ⟨B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, fun _ _ => rfl⟩
  have hβΛ : ∀ (y : ↥Λ) (w₁ w₂ : Fin 2 → k),
      β (((θ μ)⁻¹ * (θ y).adjugate * θ μ).mulVec w₁) w₂ = β w₁ ((θ y).mulVec w₂) := by
    intro y w₁ w₂
    rw [hβ, hβ, ← hθstar, he', he', hBbal]
  have hadj_add : ∀ m n : Matrix (Fin 2) (Fin 2) k, (m + n).adjugate = m.adjugate + n.adjugate := by
    intro m n; rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]
  have hadj_smul : ∀ (r : k) (m : Matrix (Fin 2) (Fin 2) k), (r • m).adjugate = r • m.adjugate := by
    intro r m; rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hσ_all : ∀ (n : Matrix (Fin 2) (Fin 2) k) (w₁ w₂ : Fin 2 → k),
      β (((θ μ)⁻¹ * n.adjugate * θ μ).mulVec w₁) w₂ = β w₁ (n.mulVec w₂) := by
    intro n w₁ w₂
    refine Submodule.span_induction (p := fun n _ => β (((θ μ)⁻¹ * n.adjugate * θ μ).mulVec w₁) w₂ = β w₁ (n.mulVec w₂))
      ?_ ?_ ?_ ?_ (hspan n)
    · rintro x ⟨y, rfl⟩; exact hβΛ y w₁ w₂
    · simp [Matrix.adjugate_zero]
    · intro x y _ _ hx hy
      rw [hadj_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec, Matrix.add_mulVec, map_add,
        LinearMap.add_apply, map_add, hx, hy]
    · intro r x _ hx
      rw [hadj_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, Matrix.smul_mulVec, map_smul,
        LinearMap.smul_apply, map_smul, hx]

  obtain ⟨c₀, hc₀⟩ := CerednikDrinfeld.SpecialModule.exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec k (θ μ) hθtr hMdet β.flip
    (fun x v w => by rw [LinearMap.flip_apply, LinearMap.flip_apply]; exact (hσ_all x w v).symm)

  have hβalt : ∀ v, β v v = 0 := by intro v; rw [hβ, hBap]; ring
  have hquad : ∀ v, c₀ * dotProduct v ((!![0, 1; -1, 0] * θ μ).mulVec v) = 0 := by
    intro v; have h := hc₀ v v; rw [LinearMap.flip_apply, hβalt] at h; exact h.symm

  have hB0 : ∀ φ ψ, B φ ψ = 0 := by
    by_cases hc0 : c₀ = 0
    · intro φ ψ
      have h := hc₀ (e ψ) (e φ)
      rw [LinearMap.flip_apply, hβ, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hc0, zero_mul] at h
      exact h
    · exfalso
      have hmv : ∀ (A : Matrix (Fin 2) (Fin 2) k) (z : Fin 2 → k) (i : Fin 2),
          A.mulVec z i = A i 0 * z 0 + A i 1 * z 1 := by
        intro A z i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have hq : ∀ v : Fin 2 → k, dotProduct v ((!![0, 1; -1, 0] * θ μ).mulVec v) = 0 :=
        fun v => (mul_eq_zero.1 (hquad v)).resolve_left hc0
      have hJ : ∀ w : Fin 2 → k, (!![(0 : k), 1; -1, 0] * θ μ).mulVec w = ![((θ μ).mulVec w) 1, -((θ μ).mulVec w) 0] := by
        intro w; rw [← Matrix.mulVec_mulVec]; ext i; fin_cases i <;> simp [hmv]
      have q0 := hq ![1, 0]
      have q1 := hq ![0, 1]
      have q2 := hq ![1, 1]
      rw [hJ] at q0 q1 q2
      simp only [hmv, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_one, mul_zero, add_zero, zero_add, one_mul, zero_mul] at q0 q1 q2
      have hM10 : θ μ 1 0 = 0 := by linear_combination q0
      have hM01 : θ μ 0 1 = 0 := by linear_combination -q1
      have hM11 : θ μ 1 1 = θ μ 0 0 := by linear_combination q2 - q0 - q1
      have hΨμ : ∀ φ : Module.Dual k ↥A₁, Ψ μ φ = (θ μ 0 0) • φ := by
        intro φ
        apply e.injective
        rw [he, map_smul]
        ext i; fin_cases i <;> simp [hmv, hM10, hM01, hM11, mul_comm]
      apply hμns
      refine ⟨θ μ 0 0, fun h hh => ?_⟩
      have hz : (⟨Φ μ h, hΦA μ h hh⟩ : ↥A₁) - (θ μ 0 0) • ⟨h, hh⟩ = 0 := by
        refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun φ => ?_
        rw [map_sub, map_smul, ← hΨ_apply μ φ ⟨h, hh⟩, hΨμ, LinearMap.smul_apply, sub_self]
      have hz' := congrArg Subtype.val hz
      simpa [sub_eq_zero] using hz'

  rw [ht]
  by_cases hc : c = 0
  · rw [hc, zero_smul]
  have hdet0 : ∀ φ ψ : Module.Dual k ↥A₁, φ ⟨a₁, ha₁⟩ * ψ ⟨a₂, ha₂⟩ = φ ⟨a₂, ha₂⟩ * ψ ⟨a₁, ha₁⟩ := by
    intro φ ψ
    have h := hB0 φ ψ
    rw [hBap] at h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc)
  by_cases h1 : (⟨a₁, ha₁⟩ : ↥A₁) = 0
  · have h1' : a₁ = 0 := by simpa using congrArg Subtype.val h1
    simp [h1']
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Module.Dual k ↥A₁, φ₀ ⟨a₁, ha₁⟩ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h1 ((Module.forall_dual_apply_eq_zero_iff k _).1 hcon)
  have hdep : (⟨a₂, ha₂⟩ : ↥A₁) = (φ₀ ⟨a₂, ha₂⟩ / φ₀ ⟨a₁, ha₁⟩) • ⟨a₁, ha₁⟩ := by
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun ψ => ?_
    rw [map_sub, map_smul, smul_eq_mul]
    have h := hdet0 φ₀ ψ
    field_simp
    linear_combination h
  have hdep' : a₂ = (φ₀ ⟨a₂, ha₂⟩ / φ₀ ⟨a₁, ha₁⟩) • a₁ := by
    have h := congrArg Subtype.val hdep
    simpa using h
  rw [hdep', TensorProduct.tmul_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul, sub_self, smul_zero]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP (solution)
