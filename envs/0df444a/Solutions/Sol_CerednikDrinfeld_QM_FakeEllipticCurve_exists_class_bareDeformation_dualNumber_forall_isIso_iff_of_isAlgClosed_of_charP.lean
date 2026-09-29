-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3eccb256-48df-5b6c-a04d-43922dca636c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Theorems.Thm_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
import Theorems.Thm_GoodReductionJacobian_exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id
import Theorems.Thm_CerednikDrinfeld_QM_exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_cls_one_endo_linearMap_pinned_unitPullback
import Theorems.Thm_Algebra_PointDerivations_exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare
import Theorems.Thm_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul
import Theorems.Thm_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isIso_of_isRegluingBy_of_exists_d_eq_sub_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare
import Theorems.Thm_CerednikDrinfeld_QM_exists_pointDerivations_linearEquiv_tensor_of_isTangentVector
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_map_tmul_sub_eq_zero_of_isRegluingBy_of_hom_bare
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_one_eq_of_charP
import Theorems.Thm_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_ringEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AdicCompletion.instIsLocalRingMaximalIdeal PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "instance" "PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"
p2m_attr_erase "simp" "SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
p2m_open "IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

set_option maxHeartbeats 8000000 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (E : FakeEllipticCurve Λ N k)

    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k (RingHom.id k)) E.f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k (RingHom.id k)) E.f, P ∈ Set.range τ ↔ IsTangentVector E.L k (RingHom.id k) P)
    (hadd : ∀ v w : V, τ (v + w) = E.L.mul (tangentBase k (RingHom.id k)) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    ∃ (H₁ : Type) (_ : AddCommGroup H₁) (_ : Module k H₁) (_ : Module.Finite k H₁) (_ : Module.finrank k H₁ = 2)
      (ρ : ↥Λ → Module.End k H₁) (θ : ↥Λ → Module.End k V)
      (cls : BareDeformation E.f E.L (DualNumber k) → V ⊗[k] H₁),

      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1) ∧
      (∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ y * ρ x) ∧

      (∀ (x : ↥Λ) (v : V), τ (θ x v) = pushPt (E.act x) (E.act_over x) (τ v)) ∧

      Function.Surjective cls ∧

      (∀ D D' : BareDeformation E.f E.L (DualNumber k), cls D = cls D' ↔ D.IsIso D') ∧

      (∀ (c : k) (D D' : BareDeformation E.f E.L (DualNumber k)) (h : D'.A ⟶ D.A),
        CategoryTheory.IsPullback h D'.f D.f
          (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)) →
        D'.g ≫ h = D.g → cls D' = c • cls D) ∧

      (∀ D : BareDeformation E.f E.L (DualNumber k),
        (∀ x : ↥Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ E.act x ≫ D.g = D.g ≫ φ) →
        ∀ x : ↥Λ, TensorProduct.map (θ x) (LinearMap.id : H₁ →ₗ[k] H₁) (cls D) =
          TensorProduct.map (LinearMap.id : V →ₗ[k] V) (ρ x) (cls D)) ∧

      (∀ ξ : V ⊗[k] H₁,
        (∀ x : ↥Λ, TensorProduct.map (θ x) (LinearMap.id : H₁ →ₗ[k] H₁) ξ =
          TensorProduct.map (LinearMap.id : V →ₗ[k] V) (ρ x) ξ) →
        ∃ (D : BareDeformation E.f E.L (DualNumber k)) (_ : SmoothOfRelativeDimension 2 D.f)
          (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f),
          ((∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D.f),
              pushPt (act x) (act_over x) (D.L.mul t P Q) =
                D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) ∧
            (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 D.A) ∧
            (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
              act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
            (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P : SchemeHomOver t D.f),
              pushPt (act (x + y)) (act_over (x + y)) P =
                D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))) ∧
          (∀ x : ↥Λ, E.act x ≫ D.g = D.g ≫ act x) ∧
          cls D = ξ) := by
  letI instAlg : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
  have halg : algebraMap (DualNumber k) k = (TrivSqZeroExt.fstHom k k k).toRingHom := rfl

  obtain ⟨hArt, hπB, hkerB, hsmallB, hIB, ⟨ιJ, hιJ, hιJI⟩, hbij, hac⟩ :=
    TrivSqZeroExt.isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber k
  haveI : IsArtinianRing (DualNumber k) := hArt
  haveI hκac : IsAlgClosed (ResidueField (DualNumber k)) := hac inferInstance
  let e : k ≃+* (ResidueField (DualNumber k)) :=
    RingEquiv.ofBijective ((residue (DualNumber k)).comp (algebraMap k (DualNumber k))) hbij
  have he : e.toRingHom = (residue (DualNumber k)).comp (algebraMap k (DualNumber k)) := rfl

  haveI : IsProper E.f := E.bundle.proper
  haveI : CompactSpace ↥E.A := QuasiCompact.compactSpace_of_compactSpace E.f
  obtain ⟨𝒦⟩ := AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace E.A
  let t₀ : ↥(Spec (CommRingCat.of k)) := ⟨⊥, Ideal.bot_prime⟩
  have ht : ∀ t : ↥(Spec (CommRingCat.of k)), t = t₀ := fun t =>
    PrimeSpectrum.ext (Ideal.eq_bot_of_prime t.asIdeal)
  have hx₀ : (E.L.one (𝟙 _)).1.base t₀ ∈ (⊤ : E.A.Opens) := trivial
  rw [← 𝒦.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hx₀
  obtain ⟨i₀, hi₀⟩ := hx₀
  let eA : Spec (CommRingCat.of k) ⟶ ↑(𝒦.U i₀) :=
    IsOpenImmersion.lift (𝒦.U i₀).ι (E.L.one (𝟙 _)).1 (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι, ht t]
      exact hi₀)
  have heA : eA ≫ (𝒦.U i₀).ι = (E.L.one (𝟙 _)).1 := IsOpenImmersion.lift_fac _ _ _

  obtain ⟨D₀, hsep, π, haffπ, hπ, hgπ, hπhom, hlift, hscal, hfib, ⟨e₀, he₀⟩⟩ :=
    GoodReductionJacobian.exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id
      k E.f E.L E.comm E.bundle 𝒦 i₀ eA heA
  haveI : IsSeparated D₀.f := hsep
  haveI : IsAffineHom π := haffπ

  have hσex := fun s : (𝒦.comap π).Idx 1 =>
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter
      D₀.f (𝒦.comap π) (ResidueField (DualNumber k)) s
  choose σ hσ₁ hσ₂ using hσex

  have hone : ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).one (𝟙 _)).1 ≫
      pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) =
      specMap (DualNumber k) (ResidueField (DualNumber k)) ≫ (D₀.L.one (𝟙 _)).1 := by
    rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    have h1 := congrArg Subtype.val
      (D₀.L.one_natural (𝟙 _) (𝟙 _ ≫ specMap (DualNumber k) (ResidueField (DualNumber k))) (specMap (DualNumber k) (ResidueField (DualNumber k))) (by simp))
    exact h1.symm
  let e₁ : Spec (CommRingCat.of (ResidueField (DualNumber k))) ⟶ ↑(((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀) :=
    IsOpenImmersion.lift (((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀).ι
      ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).one (𝟙 _)).1 (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h2 : (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))
          (((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).one (𝟙 _)).1 t) =
          (D₀.L.one (𝟙 _)).1 ((specMap (DualNumber k) (ResidueField (DualNumber k))) t) := by
        have := congrArg (fun φ : Spec (CommRingCat.of (ResidueField (DualNumber k))) ⟶ D₀.A => φ t) hone
        simpa only [Scheme.Hom.comp_apply] using this
      show (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))
          (((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).one (𝟙 _)).1 t) ∈ (𝒦.comap π).U i₀
      rw [h2, ← he₀, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (e₀ ((specMap (DualNumber k) (ResidueField (DualNumber k))) t)).2)
  have he₁ : e₁ ≫ (((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀).ι =
      ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).one (𝟙 _)).1 :=
    IsOpenImmersion.lift_fac _ _ _

  have hbot : specMap (DualNumber k) (ResidueField (DualNumber k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) =
      Spec.map (CommRingCat.ofHom e.toRingHom) := by
    rw [he, ← Spec.map_comp]
    rfl
  have hcart : IsPullback ((pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ π) (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) E.f (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    rw [← hbot]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) hπ

  have mul_congr : ∀ {T : Scheme.{0}} (t₁ t₂ : T ⟶ Spec (CommRingCat.of k)) (h12 : t₁ = t₂)
      (x y : SchemeHomOver t₁ E.f),
      (E.L.mul t₁ x y).1 = (E.L.mul t₂ ⟨x.1, h12 ▸ x.2⟩ ⟨y.1, h12 ▸ y.2⟩).1 := by
    intro T t₁ t₂ h12 x y; subst h12; rfl
  have himul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (ResidueField (DualNumber k)))) (P Q : SchemeHomOver t' (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
      ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).mul t' P Q).1 ≫ ((pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ π) =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
          ⟨P.1 ≫ ((pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ π), by rw [Category.assoc, hcart.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ ((pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ π), by rw [Category.assoc, hcart.w, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' P Q
    rw [← Category.assoc, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
      hπhom]
    rw [mul_congr _ _ (by rw [Category.assoc, hbot])]
    simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc]
  haveI hAκ : AbelianSchemePropertyBundle (ResidueField (DualNumber k)) (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_ringEquiv e E.f (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ((pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ π) hcart (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L) E.bundle
  have hcκ : (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).IsCommutative := RelativeGroupLaw.IsCommutative.baseChange _ D₀.comm
  haveI : SmoothOfRelativeDimension 2 E.f := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 2) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 2
  haveI : SmoothOfRelativeDimension 2 (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 2) hcart inferInstance
  haveI : IsProper D₀.f := D₀.bundle.proper
  haveI : LocallyOfFiniteType (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) := inferInstance
  haveI : CharP (ResidueField (DualNumber k)) ℓ := charP_of_injective_ringHom (f := e.toRingHom) e.injective ℓ

  letI instκV : Module (ResidueField (DualNumber k)) V := Module.compHom V (e.symm : (ResidueField (DualNumber k)) ≃+* k).toRingHom
  obtain ⟨τκ, hκinj, hκrange, hκadd, hκsmul, hκiff⟩ :=
    CerednikDrinfeld.QM.exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv e E.f (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) E.L (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L)
      ((pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ π) hcart himul V τ hinj hrange hadd hsmul

  letI instAlgU := algebraOfHom (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) (((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀)
  obtain ⟨Φ, hΦnat, hΦpin⟩ :=
    CerednikDrinfeld.QM.exists_pointDerivations_linearEquiv_tensor_of_isTangentVector (ResidueField (DualNumber k)) (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L)
      (((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀) (((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).isAffineOpen i₀) e₁ he₁ V τκ hκinj hκrange hκadd hκsmul

  obtain ⟨H₁, iH₁a, iH₁m, iH₁f, hfr, cls₁, ρ, hcls₁, hcls₁0, hρid, hρcomp, hρadd, hρpin⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_cls_one_endo_linearMap_pinned_unitPullback
      (ResidueField (DualNumber k)) (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L) hAκ ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k)))
  have hdim : (OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).cechFinrank ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1 = 2 :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_one_eq_of_charP (ResidueField (DualNumber k)) ℓ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L) hcκ hAκ 2 ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k)))

  obtain ⟨Ψ, hΨlift, hΨpin, hΨeq, hΨsurj, hΨpre⟩ :=
    Algebra.PointDerivations.exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor (ResidueField (DualNumber k))
      Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀)
      ((((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField (DualNumber k)))).hom).hom
      V Φ hΦnat ((OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).d ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 0) ((OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).d ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1)
      H₁ cls₁ hcls₁ hcls₁0 (ResidueField (DualNumber k))
  letI instkH : Module k (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) := Module.compHom (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) e.toRingHom
  letI instkVH : Module k (V ⊗[(ResidueField (DualNumber k))] (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁)) := Module.compHom (V ⊗[(ResidueField (DualNumber k))] (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁)) e.toRingHom
  obtain ⟨hfinK, hfrK, Θ, hΘtmul, hΘmap⟩ :=
    TensorProduct.exists_linearEquiv_compHom_ringEquiv_tmul e V (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁)

  have hG8 := fun D : BareDeformation E.f E.L (DualNumber k) =>
    GoodReductionJacobian.BareDeformation.exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare
      (DualNumber k) k hπB hkerB hsmallB E.f E.L E.comm E.bundle hIB (ResidueField (DualNumber k)) ιJ hιJ hιJI D₀ (𝒦.comap π) i₀ e₀ he₀
      e₁ he₁ σ hσ₁ hσ₂ D
  choose τD cD hcD hRD hτD using hG8
  let cls : BareDeformation E.f E.L (DualNumber k) → V ⊗[k] (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) := fun D => Θ.symm (Ψ (cD D))

  obtain ⟨θ, hθτ, hθadd, hθone, hθmul, hθuniq⟩ :=
    CerednikDrinfeld.QM.exists_moduleEnd_apply_eq_pushPt_of_isTangentVector E.L E.act E.act_over E.act_hom
      E.act_one E.act_mul E.act_add k (RingHom.id k) V τ hinj hrange hadd hsmul
  have hL := fun x : ↥Λ => hlift (E.act x) (E.act_over x)
  choose φ₀ hφ₀f hφ₀g hφ₀π hφ₀hom using hL
  have hF := fun x : ↥Λ => hfib (φ₀ x) (hφ₀f x)
  choose ψ hψf hψ₀ hψhom using hF

  let resK : ((Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) →ₗ[(ResidueField (DualNumber k))] (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁)) → ((Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) →ₗ[k] (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁)) := fun g =>
    { toFun := g, map_add' := g.map_add, map_smul' := fun c m => g.map_smul (e c) m }
  let ρk : ↥Λ → Module.End k (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) := fun x =>
    resK (LinearMap.llcomp (ResidueField (DualNumber k)) (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k))) H₁ H₁ (ρ (ψ x) (hψf x)))
  haveI : Module.Finite k (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) := hfinK.mpr inferInstance
  have hfr2 : Module.finrank k (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) = 2 := by
    rw [hfrK, Module.finrank_linearMap, hfr, hdim]
    simp

  have φ₀_unique : ∀ (a b : D₀.A ⟶ D₀.A), a ≫ π = b ≫ π → a ≫ D₀.f = b ≫ D₀.f → a = b :=
    fun a b h1 h2 => hπ.hom_ext h1 h2
  have ψ_unique : ∀ (a b : (pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ⟶ (pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
      a ≫ (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) = b ≫ (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) → a ≫ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) = b ≫ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) → a = b :=
    fun a b h1 h2 => pullback.hom_ext h1 h2
  have ρ_congr : ∀ (a b : (pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ⟶ (pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))) (hab : a = b) (ha : a ≫ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) = (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))) (hb : b ≫ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) = (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
      ρ a ha = ρ b hb := by
    intro a b hab ha hb; subst hab; rfl

  have hφ₀π' : ∀ (x : ↥Λ) {Z : Scheme.{0}} (g : E.A ⟶ Z), φ₀ x ≫ π ≫ g = π ≫ E.act x ≫ g := by
    intro x Z g; rw [← Category.assoc, hφ₀π, Category.assoc]
  have hψ₀' : ∀ (x : ↥Λ) {Z : Scheme.{0}} (g : D₀.A ⟶ Z), ψ x ≫ (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ g = (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ φ₀ x ≫ g := by
    intro x Z g; rw [← Category.assoc, hψ₀, Category.assoc]
  have hφ₀f' : ∀ (x : ↥Λ) {Z : Scheme.{0}} (g : Spec (CommRingCat.of (DualNumber k)) ⟶ Z), φ₀ x ≫ D₀.f ≫ g = D₀.f ≫ g := by
    intro x Z g; rw [← Category.assoc, hφ₀f]
  have hψf' : ∀ (x : ↥Λ) {Z : Scheme.{0}} (g : Spec (CommRingCat.of (ResidueField (DualNumber k))) ⟶ Z), ψ x ≫ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ g = (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ≫ g := by
    intro x Z g; rw [← Category.assoc, hψf]

  have hφ₀one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ₀ ⟨1, h1⟩ = 𝟙 D₀.A := by
    intro h1
    apply φ₀_unique
    · rw [hφ₀π, E.act_one h1, Category.id_comp, Category.comp_id]
    · rw [hφ₀f, Category.id_comp]
  have hψone : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ψ ⟨1, h1⟩ = 𝟙 _ := by
    intro h1
    apply ψ_unique
    · rw [hψ₀, hφ₀one h1, Category.id_comp, Category.comp_id]
    · rw [hψf, Category.id_comp]
  have hφ₀mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ₀ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = φ₀ y ≫ φ₀ x := by
    intro x y hxy
    apply φ₀_unique
    · simp only [Category.assoc, hφ₀π, hφ₀π', E.act_mul x y hxy]
    · simp only [Category.assoc, hφ₀f, hφ₀f']
  have hψmul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = ψ y ≫ ψ x := by
    intro x y hxy
    apply ψ_unique
    · simp only [Category.assoc, hψ₀, hψ₀', hφ₀mul x y hxy]
    · simp only [Category.assoc, hψf, hψf']
  have resK_apply : ∀ (g : (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁) →ₗ[(ResidueField (DualNumber k))] (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁)) (F : (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁)), resK g F = g F := fun g F => rfl

  have T3 := GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare (DualNumber k) k hπB hkerB hsmallB E.f E.L E.comm E.bundle hIB (ResidueField (DualNumber k)) ιJ hιJ hιJI D₀ (𝒦.comap π) i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂
  have T4 := GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_exists_d_eq_sub_bare (DualNumber k) k hπB hkerB hsmallB E.f E.L E.comm E.bundle hIB (ResidueField (DualNumber k)) ιJ hιJ hιJI D₀ (𝒦.comap π) i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂
  have T5 := GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare (DualNumber k) k hπB hkerB hsmallB E.f E.L E.comm E.bundle hIB (ResidueField (DualNumber k)) ιJ hιJ hιJI D₀ (𝒦.comap π) i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂
  have S4 := GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_map_tmul_sub_eq_zero_of_isRegluingBy_of_hom_bare (DualNumber k) k hπB hkerB hsmallB E.f E.L E.comm E.bundle hIB (ResidueField (DualNumber k)) ιJ hιJ hιJI D₀ (𝒦.comap π) i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂

  let θκ : ↥Λ → (V →ₗ[(ResidueField (DualNumber k))] V) := fun x =>
    { toFun := θ x, map_add' := (θ x).map_add, map_smul' := fun a' v => (θ x).map_smul ((e.symm : (ResidueField (DualNumber k)) ≃+* k) a') v }
  have hθκ : ∀ (x : ↥Λ) (w : V), τκ (θκ x w) = pushPt (ψ x) (hψf x) (τκ w) := by
    intro x w
    exact ((hκiff (E.act x) (E.act_over x) (ψ x) (hψf x) (by simp only [Category.assoc, hψ₀', hφ₀π]) w (θ x w)).1
      (hθτ x w))
  haveI : SmoothOfRelativeDimension 2 D₀.f :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 2) hπ inferInstance
  have hcDm : ∀ (D : BareDeformation E.f E.L (DualNumber k)) (a : Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀))
      (ξ : Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k))),
      (cD D : Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀) →ₗ[(ResidueField (DualNumber k))]
        (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).cochain ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1)) a ξ ∈
        LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).d ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1) :=
    fun D a ξ => LinearMap.mem_ker.mpr (hcD D a ξ)
  refine ⟨(Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] H₁), inferInstance, instkH, inferInstance, hfr2, ρk, θ, cls, ?_, ?_, ?_, hθτ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    apply LinearMap.ext; intro F; apply LinearMap.ext; intro ξ
    show resK _ F ξ = F ξ
    rw [resK_apply, LinearMap.llcomp_apply, ρ_congr _ _ (hψone h1) (hψf _) (Category.id_comp _), hρid, LinearMap.id_apply]
  ·
    intro x y
    have hsum : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField (DualNumber k)))) (P : SchemeHomOver t (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
        P.1 ≫ ψ (x + y) = ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψf]; exact P.2⟩
          ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψf]; exact P.2⟩).1 := by
      intro T t P
      apply pullback.hom_ext
      · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
          Category.assoc, hψ₀]
        apply hπ.hom_ext
        · rw [Category.assoc, Category.assoc, hφ₀π, hπhom]
          have h3 := congrArg Subtype.val (E.act_add x y
            ((t ≫ specMap (DualNumber k) (ResidueField (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
            ⟨(P.1 ≫ (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))) ≫ π, by rw [Category.assoc, Category.assoc, hπ.w, ← Category.assoc (pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))),
              pullback.condition, Category.assoc, ← Category.assoc P.1, P.2, Category.assoc]⟩)
          simp only [pushPt, mapPt_coe, Category.assoc] at h3
          rw [h3]
          congr 2 <;> apply Subtype.ext <;>
            simp only [mapPt_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hψ₀', hφ₀π]
        · rw [(D₀.L.mul _ _ _).2, Category.assoc, Category.assoc, hφ₀f, pullback.condition, ← Category.assoc, P.2]
      · rw [Category.assoc, hψf, ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).mul t _ _).2]
        exact P.2
    apply LinearMap.ext; intro F; apply LinearMap.ext; intro ξ
    show resK _ F ξ = (resK _ F + resK _ F) ξ
    rw [LinearMap.add_apply, resK_apply, resK_apply, resK_apply, LinearMap.llcomp_apply, LinearMap.llcomp_apply,
      LinearMap.llcomp_apply, hρadd (ψ x) (ψ y) (ψ (x + y)) (hψf x) (hψf y) (hψf _) hsum, LinearMap.add_apply]
  ·
    intro x y hxy
    apply LinearMap.ext; intro F; apply LinearMap.ext; intro ξ
    show resK _ F ξ = resK _ (resK _ F) ξ
    rw [resK_apply, resK_apply, resK_apply, LinearMap.llcomp_apply, LinearMap.llcomp_apply, LinearMap.llcomp_apply,
      ρ_congr _ _ (hψmul x y hxy) (hψf _) (by rw [Category.assoc, hψf, hψf]), hρcomp, LinearMap.comp_apply]
  ·
    intro ξ
    obtain ⟨c, hc, hcw⟩ := hΨsurj (Θ ξ)
    obtain ⟨τ', D, hD, hτ'⟩ := T3 c hc
    refine ⟨D, ?_⟩
    show Θ.symm (Ψ (cD D)) = ξ
    rw [(hΨeq (cD D) c (hcDm D) hc).2 (T5 (cD D) (hcDm D) c hc (τD D) τ' D D (hRD D) hD (hτD D) hτ'
      ⟨Iso.refl _, by simp, by simp⟩), hcw, LinearEquiv.symm_apply_apply]
  ·
    intro D D'
    constructor
    · intro h
      have h1 : Ψ (cD D) = Ψ (cD D') :=
        Θ.symm.injective (show Θ.symm (Ψ (cD D)) = Θ.symm (Ψ (cD D')) from h)
      exact T4 (cD D) (hcDm D) (cD D') (hcDm D') (τD D) (τD D') D D' (hRD D) (hRD D') (hτD D) (hτD D')
        ((hΨeq (cD D) (cD D') (hcDm D) (hcDm D')).1 h1)
    · intro hiso
      show Θ.symm (Ψ (cD D)) = Θ.symm (Ψ (cD D'))
      rw [(hΨeq (cD D) (cD D') (hcDm D) (hcDm D')).2
        (T5 (cD D) (hcDm D) (cD D') (hcDm D') (τD D) (τD D') D D' (hRD D) (hRD D') (hτD D) (hτD D') hiso)]
  ·
    intro c D D' h hh hhg
    have S1 := GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare
      (DualNumber k) k hπB hkerB hsmallB E.f E.L E.comm E.bundle hIB (ResidueField (DualNumber k)) ιJ hιJ hιJI D₀ (𝒦.comap π) i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂

    obtain ⟨φc, hφc⟩ : ∃ φc : DualNumber k →+* DualNumber k,
        φc = (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom := ⟨_, rfl⟩
    have hφcB : (algebraMap (DualNumber k) k).comp φc = algebraMap (DualNumber k) k := by
      apply RingHom.ext; intro z
      rw [halg, hφc]
      simp
    have hφcJ : ∀ v : (ResidueField (DualNumber k)), ιJ ((e c • (LinearMap.id : (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (ResidueField (DualNumber k)))) v) = φc (ιJ v) := by
      intro v
      have hmem : ιJ v ∈ RingHom.ker (algebraMap (DualNumber k) k) := by
        have : ιJ v ∈ LinearMap.range ιJ := ⟨v, rfl⟩
        rw [hιJI] at this; exact this
      rw [RingHom.mem_ker, halg] at hmem
      have hmem' : TrivSqZeroExt.fst (ιJ v) = 0 := by simpa using hmem
      have hsm : (e c • (LinearMap.id : (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (ResidueField (DualNumber k)))) v = (algebraMap k (DualNumber k) c) • v := by
        rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]
        rfl
      rw [hsm, LinearMap.map_smul, hφc]
      obtain ⟨m, hm⟩ : ∃ m : k, ιJ v = TrivSqZeroExt.inr m := ⟨TrivSqZeroExt.snd (ιJ v), by ext <;> simp [hmem']⟩
      rw [hm, TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul, TrivSqZeroExt.inl_mul_inr]
      apply TrivSqZeroExt.ext <;> simp [mul_comm]
    obtain ⟨k₀, hk₀, hk₀g, hk₀π, hk₀κ⟩ := hscal c
    have hk₀U : ∀ i : (𝒦.comap π).ι, k₀ ⁻¹ᵁ (𝒦.comap π).U i = (𝒦.comap π).U i := by
      intro i
      show k₀ ⁻¹ᵁ (π ⁻¹ᵁ 𝒦.U i) = π ⁻¹ᵁ 𝒦.U i
      rw [← Scheme.Hom.comp_preimage, hk₀π]
    obtain ⟨τ', hD', hτ'⟩ := S1 (cD D) (hcDm D) φc hφcB (e c • LinearMap.id) hφcJ k₀ (by rw [hφc]; exact hk₀) hk₀g hk₀U hk₀κ
      (τD D) D (hRD D) (hτD D) D' h (by rw [hφc]; exact hh) hhg

    let c' := Algebra.PointDerivations.map
      ((((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField (DualNumber k)))).hom).hom
      (LinearMap.lcomp (ResidueField (DualNumber k)) ((OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).cochain ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1)
        (LinearMap.dualMap (e c • (LinearMap.id : (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (ResidueField (DualNumber k)))))) (cD D)
    have hc' : ∀ (a' : Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀)) (ξ : Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k))),
        (c' : Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀) →ₗ[(ResidueField (DualNumber k))]
          (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).cochain ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1)) a' ξ =
        (cD D : Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀) →ₗ[(ResidueField (DualNumber k))]
          (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).cochain ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1)) a'
          (ξ ∘ₗ (e c • (LinearMap.id : (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (ResidueField (DualNumber k))))) := fun a' ξ => rfl
    have hc'm : ∀ (a' : Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀)) (ξ : Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k))),
        (c' : Γ((pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))), ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).U i₀) →ₗ[(ResidueField (DualNumber k))]
          (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).cochain ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1)) a' ξ ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))).d ((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))) 1) := fun a' ξ => by rw [hc']; exact hcDm D _ _
    have hΨD' : Ψ (cD D') = Ψ c' :=
      (hΨeq (cD D') c' (hcDm D') hc'm).2
        (T5 (cD D') (hcDm D') c' hc'm (τD D') τ' D' D' (hRD D') hD' (hτD D') hτ' ⟨Iso.refl _, by simp, by simp⟩)
    have hT : Ψ c' = _root_.TensorProduct.map (LinearMap.id : V →ₗ[(ResidueField (DualNumber k))] V) (e c • LinearMap.id) (Ψ (cD D)) :=
      hΨpre (cD D) c' (e c • LinearMap.id) (e c • LinearMap.id) (fun F ξ => by
        have hξ : ξ ∘ₗ (e c • (LinearMap.id : (ResidueField (DualNumber k)) →ₗ[(ResidueField (DualNumber k))] (ResidueField (DualNumber k)))) = e c • ξ := by
          ext
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
            smul_eq_mul, mul_one]
          rw [show ξ (e c) = ξ (e c • (1 : (ResidueField (DualNumber k)))) by rw [smul_eq_mul, mul_one], LinearMap.map_smul, smul_eq_mul]
        rw [hξ, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.id_apply]
        rfl) (hcDm D) hc'
    show Θ.symm (Ψ (cD D')) = c • Θ.symm (Ψ (cD D))
    rw [hΨD', hT, TensorProduct.map_smul_right, LinearMap.smul_apply, TensorProduct.map_id, LinearMap.id_apply]
    exact Θ.symm.map_smul c (Ψ (cD D))
  ·
    intro D hlifts x
    obtain ⟨ĉ, hĉ⟩ := hΨlift (cD D) (hcDm D)
    have h4 := S4 (cD D) (hcDm D) (τD D) D (hRD D) (hτD D) (((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).isAffineOpen i₀) V τκ hκinj hκrange hκadd hκsmul
      Φ hΦnat hΦpin (E.act x) (E.act_over x) (φ₀ x) (hφ₀f x) (hφ₀g x) (ψ x) (hψf x)
      (hψhom x (hφ₀hom x (E.act_hom x))) (hψ₀ x) (θκ x) (hθκ x) H₁ cls₁ hcls₁ hcls₁0 (ρ (ψ x) (hψf x))
      (hρpin (ψ x) (hψf x)) ĉ hĉ
    rw [← hΨpin (cD D) ĉ hĉ, sub_eq_zero] at h4
    have h5 := h4.1 (hlifts x)
    apply Θ.injective
    show Θ (_root_.TensorProduct.map (θ x) LinearMap.id (Θ.symm (Ψ (cD D)))) =
      Θ (_root_.TensorProduct.map LinearMap.id (ρk x) (Θ.symm (Ψ (cD D))))
    rw [hΘmap (θ x) (θκ x) (fun v => rfl) LinearMap.id LinearMap.id (fun h => rfl),
      hΘmap LinearMap.id LinearMap.id (fun v => rfl)
        (LinearMap.llcomp (ResidueField (DualNumber k)) (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k))) H₁ H₁ (ρ (ψ x) (hψf x))) (ρk x) (fun h => rfl),
      LinearEquiv.apply_symm_apply]
    exact h5
  ·
    intro ξ hξ
    obtain ⟨c, hc, hcw⟩ := hΨsurj (Θ ξ)
    obtain ⟨τ', D, hD, hτ'⟩ := T3 c hc
    have hclsD : cls D = ξ := by
      show Θ.symm (Ψ (cD D)) = ξ
      rw [(hΨeq (cD D) c (hcDm D) hc).2 (T5 (cD D) (hcDm D) c hc (τD D) τ' D D (hRD D) hD (hτD D) hτ'
        ⟨Iso.refl _, by simp, by simp⟩), hcw, LinearEquiv.symm_apply_apply]
    have hlifts : ∀ x : ↥Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ E.act x ≫ D.g = D.g ≫ φ := by
      intro x
      obtain ⟨ĉ, hĉ⟩ := hΨlift c hc
      have h4 := S4 c hc τ' D hD hτ' (((𝒦.comap π).baseChange D₀.f (ResidueField (DualNumber k))).isAffineOpen i₀) V τκ hκinj hκrange hκadd hκsmul
        Φ hΦnat hΦpin (E.act x) (E.act_over x) (φ₀ x) (hφ₀f x) (hφ₀g x) (ψ x) (hψf x)
        (hψhom x (hφ₀hom x (E.act_hom x))) (hψ₀ x) (θκ x) (hθκ x) H₁ cls₁ hcls₁ hcls₁0 (ρ (ψ x) (hψf x))
        (hρpin (ψ x) (hψf x)) ĉ hĉ
      rw [← hΨpin c ĉ hĉ, sub_eq_zero] at h4
      apply h4.2
      rw [hcw, ← hΘmap (θ x) (θκ x) (fun v => rfl) LinearMap.id LinearMap.id (fun h => rfl),
        ← hΘmap LinearMap.id LinearMap.id (fun v => rfl)
          (LinearMap.llcomp (ResidueField (DualNumber k)) (Module.Dual (ResidueField (DualNumber k)) (ResidueField (DualNumber k))) H₁ H₁ (ρ (ψ x) (hψf x))) (ρk x) (fun h => rfl),
        hξ x]
    obtain ⟨act, act_over, hlaws, hcompat⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
        (DualNumber k) k hπB hkerB E D hlifts
    exact ⟨D, GoodReductionJacobian.BareDeformation.smoothOfRelativeDimension_of_isRegluingBy D₀ (𝒦.comap π) τ' D hD 2,
      act, act_over, hlaws, hcompat, hclsD⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP (solution)
