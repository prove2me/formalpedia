-- Prove2me | solution 1 for DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0c907a50-895c-59f7-9e69-26adc61702b8

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
import Theorems.Thm_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions Deep.NTSupply.instNormalRayClassSubgroup AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar"
p2m_attr_erase "instance" "AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "instance" "instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic LocalNewvector.instSMulCommClassComplexGeneralLinearGroupFinOfNatNatPadicAdelicSpanRat LocalNewvector.instDistribMulActionGeneralLinearGroupFinOfNatNatPadicAdelicSpanRat LocalNewvector.AdelicFnCarrier.instSMulCommClassComplexAdelicGL2RingOfIntegers LocalNewvector.AdelicSpan.instModuleComplex LocalNewvector.AdelicFnCarrier.instDistribMulActionAdelicGL2RingOfIntegers LocalNewvector.instDistribMulActionGeneralLinearGroupFinOfNatNatPadicAdelicFnCarrierRat LocalNewvector.AdelicSpan.instDistribMulActionAdelicGL2RingOfIntegers LocalNewvector.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplexAdelicFnCarrierRat LocalNewvector.AdelicSpan.instSMulCommClassAdelicGL2RingOfIntegersComplex LocalNewvector.AdelicFnCarrier.instAddCommGroup LocalNewvector.AdelicSpan.instAddCommGroup LocalNewvector.AdelicSpan.instSMulCommClassComplexAdelicGL2RingOfIntegers LocalNewvector.AdelicFnCarrier.instModuleComplex LocalNewvector.instSMulCommClassComplexGeneralLinearGroupFinOfNatNatPadicAdelicFnCarrierRat LocalNewvector.AdelicFnCarrier.instSMulCommClassAdelicGL2RingOfIntegersComplex LocalNewvector.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplexAdelicSpanRat HeckeIntegralSeam.finite_padicInt_quotient_span_p LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SpectralSide.instCompactSpaceMatrix instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulAlgEquiv Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.whittakerCoefficient_zero"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff"
p2m_attr_erase "simp" "M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.AdelicSpan.toFn_smul LocalNewvector.AdelicFnCarrier.toFn_csmul LocalNewvector.AdelicFnCarrier.toFn_add LocalNewvector.AdelicFnCarrier.toFn_mk LocalNewvector.AdelicFnCarrier.toFn_smul LocalNewvector.AdelicFnCarrier.toFn_zero LocalNewvector.AdelicFnCarrier.mk_toFn LocalNewvector.AdelicSpan.toFn_self LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one"
p2m_attr_erase "simp" "Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"

set_option autoImplicit false

open scoped BigOperators

namespace DeligneSerre55

theorem isIntegral_of_mem (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] {x : ℂ} (hx : x ∈ R) :
    IsIntegral ℤ x := by
  have h : IsIntegral ℤ (⟨x, hx⟩ : R) := Algebra.IsIntegral.isIntegral _
  simpa using h.map R.val

theorem exists_intermediateField (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ (R : Set ℂ) ⊆ K := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite ℤ R)
  let S : Set ℂ := (s.image (fun x : R => (x : ℂ)) : Finset ℂ)
  haveI : Finite S := Finset.finite_toSet _ |>.to_subtype
  have hSint : ∀ x ∈ S, IsIntegral ℚ x := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact (isIntegral_of_mem R y.2).tower_top
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hSint, ?_⟩
  intro x hx
  have hxs : (⟨x, hx⟩ : R) ∈ Submodule.span ℤ (s : Set R) := by rw [hs]; trivial
  suffices h : ∀ y : R, y ∈ Submodule.span ℤ (s : Set R) →
      (y : ℂ) ∈ IntermediateField.adjoin ℚ S from h _ hxs
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      exact IntermediateField.subset_adjoin ℚ S
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
  | zero => simp
  | add a b _ _ ha hb => simpa using (IntermediateField.adjoin ℚ S).add_mem ha hb
  | smul n a _ ha => simpa using zsmul_mem ha n

theorem isIntegral_coe_intermediateField (K : IntermediateField ℚ ℂ) (x : K)
    (hx : IsIntegral ℤ (x : ℂ)) : IsIntegral ℤ x := by
  obtain ⟨q, hqm, hq⟩ := hx
  refine ⟨q, hqm, ?_⟩
  have h := Polynomial.hom_eval₂ q (algebraMap ℤ K) (K.val.toRingHom) x
  have h1 : (K.val.toRingHom).comp (algebraMap ℤ K) = algebraMap ℤ ℂ := Subsingleton.elim _ _
  rw [h1] at h
  have h2 : (K.val.toRingHom) (Polynomial.eval₂ (algebraMap ℤ K) x q) = 0 := by
    rw [h]; exact hq
  exact (map_eq_zero_iff _ Subtype.val_injective).mp h2

theorem lt_log_one_div_sub_one {M s : ℝ} (hs1 : 1 < s) (hs : s < 1 + Real.exp (-M)) :
    M < Real.log (1 / (s - 1)) := by
  have hpos : 0 < s - 1 := by linarith
  have hlt : s - 1 < Real.exp (-M) := by linarith
  have hlog : Real.log (s - 1) < -M := (Real.log_lt_iff_lt_exp hpos).mpr hlt
  rw [one_div, Real.log_inv]
  linarith

theorem log_one_div_sub_one_pos {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    0 < Real.log (1 / (s - 1)) := by
  apply Real.log_pos
  rw [lt_div_iff₀ (by linarith)]
  linarith

open ModularFormClass CongruenceSubgroup
open scoped MatrixGroups

theorem main
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R) ∧
      ∀ η : ℝ, 0 < η → ∃ (Y : Finset ℂ) (X : Set ℕ),
        (∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
          ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
            (η + δ) * Real.log (1 / (s - 1))) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ X → ModularFormClass.qCoeff f p ∈ Y := by
  classical

  obtain ⟨R, hfin, hR, hε, hconj⟩ :=
    DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
      N ε f hf₁ hT
  haveI : Module.Finite ℤ R := hfin

  obtain ⟨K, hKfd, hRK⟩ := exists_intermediateField R
  haveI : FiniteDimensional ℚ K := hKfd
  haveI : NumberField K := NumberField.mk

  let ι : R →+* K :=
    { toFun := fun x => ⟨x.1, hRK x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  have hι : ∀ x : R, ((ι x : K) : ℂ) = (x : ℂ) := fun x => rfl

  choose ε' g hε' hg₁ hgp hgT using fun φ : K →+* ℂ => hconj (φ.comp ι)

  choose C hC using fun φ : K →+* ℂ =>
    DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
      N (ε' φ) (g φ) (hg₁ φ) (hgT φ)

  have haK : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (φ : K →+* ℂ),
      φ ⟨qCoeff f p, hRK (hR p hp hpN)⟩ = qCoeff (g φ) p := by
    intro p hp hpN φ
    rw [hgp φ p hp hpN]
    rfl
  refine ⟨R, hfin, hR, fun η hη => ?_⟩

  set r : ℕ := Fintype.card (K →+* ℂ) with hr_def
  have hr : 0 < r := Fintype.card_pos
  set c : ℝ := r / η with hc_def
  have hc : 0 < c := div_pos (Nat.cast_pos.mpr hr) hη
  have hrc : (r : ℝ) / c = η := by
    rw [hc_def]; field_simp
  set B : ℝ := Real.sqrt c with hB_def

  let F : Finset K := (NumberField.Embeddings.finite_of_norm_le K ℂ B).toFinset
  let Y : Finset ℂ := F.image (fun x : K => (x : ℂ))

  let X : Set ℕ := {p | p.Prime ∧ ¬ p ∣ N ∧ ∃ φ : K →+* ℂ, c < ‖qCoeff (g φ) p‖ ^ 2}
  refine ⟨Y, X, ?_, ?_⟩
  ·
    intro δ hδ
    set Ctot : ℝ := ∑ φ : K →+* ℂ, C φ with hCtot_def
    set M : ℝ := max Ctot 0 / (c * δ) with hM_def
    have hM0 : 0 ≤ M := div_nonneg (le_max_right _ _) (mul_pos hc hδ).le
    refine ⟨1 + Real.exp (-M), by linarith [Real.exp_pos (-M)], fun s hs1 hs0 => ?_⟩
    have hexp1 : Real.exp (-M) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hM0)
    have hs2 : s < 2 := by linarith
    set L : ℝ := Real.log (1 / (s - 1)) with hL_def
    have hML : M < L := lt_log_one_div_sub_one hs1 hs0
    have hL0 : 0 < L := log_one_div_sub_one_pos hs1 hs2

    let PN := {p : ℕ // p.Prime ∧ ¬ p ∣ N}
    let PX := {p : ℕ // p.Prime ∧ p ∈ X}

    let G : PN → ℝ := fun p => ∑ φ : K →+* ℂ, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
    have hGs : Summable G := summable_sum fun φ _ => (hC φ s hs1 hs2).1
    have hGt : ∑' p, G p = ∑ φ : K →+* ℂ,
        ∑' p : PN, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) :=
      Summable.tsum_finsetSum fun φ _ => (hC φ s hs1 hs2).1
    have hGle : ∑' p, G p ≤ r * L + Ctot := by
      rw [hGt]
      calc ∑ φ : K →+* ℂ, ∑' p : PN, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
          ≤ ∑ φ : K →+* ℂ, (L + C φ) := Finset.sum_le_sum fun φ _ => (hC φ s hs1 hs2).2
        _ = r * L + Ctot := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

    let e : PX → PN := fun p => ⟨p.1, p.2.1, p.2.2.2.1⟩
    have he : Function.Injective e := by
      intro p q hpq
      apply Subtype.ext
      have := congrArg Subtype.val hpq
      exact this
    have hsumX : Summable (fun p : PX => c * ((p : ℕ) : ℝ) ^ (-s)) := by
      have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
        Real.summable_nat_rpow.mpr (by linarith)
      exact (h0.subtype {p : ℕ | p.Prime ∧ p ∈ X}).mul_left c
    have hGnonneg : ∀ q : PN, 0 ≤ G q := fun q =>
      Finset.sum_nonneg fun φ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hterm : ∀ p : PX, c * ((p : ℕ) : ℝ) ^ (-s) ≤ G (e p) := by
      intro p
      obtain ⟨hp, hpN, φ₀, hφ₀⟩ := p.2.2
      show c * ((p : ℕ) : ℝ) ^ (-s) ≤
        ∑ φ : K →+* ℂ, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      refine hφ₀.le.trans ?_
      exact Finset.single_le_sum (f := fun φ : K →+* ℂ => ‖qCoeff (g φ) (p : ℕ)‖ ^ 2)
        (fun φ _ => sq_nonneg _) (Finset.mem_univ φ₀)
    have hcmp : ∑' p : PX, c * ((p : ℕ) : ℝ) ^ (-s) ≤ ∑' q, G q :=
      Summable.tsum_le_tsum_of_inj e he (fun q _ => hGnonneg q) hterm hsumX hGs
    rw [tsum_mul_left] at hcmp

    have hmain : c * ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ r * L + Ctot := hcmp.trans hGle
    have h1 : ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ η * L + Ctot / c := by
      have h1' : ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ (r * L + Ctot) / c := by
        rw [le_div_iff₀ hc]; linarith [hmain]
      calc ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ (r * L + Ctot) / c := h1'
        _ = (r : ℝ) / c * L + Ctot / c := by ring
        _ = η * L + Ctot / c := by rw [hrc]
    have h2 : Ctot / c ≤ δ * L := by
      have h3 : Ctot / c ≤ max Ctot 0 / c := div_le_div_of_nonneg_right (le_max_left _ _) hc.le
      have h4 : max Ctot 0 / c = δ * M := by
        rw [hM_def]; field_simp
      rw [h4] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left hML.le hδ.le)
    calc ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ η * L + Ctot / c := h1
      _ ≤ η * L + δ * L := by linarith
      _ = (η + δ) * L := by ring
  ·
    intro p hp hpN hpX
    have hall : ∀ φ : K →+* ℂ, ‖qCoeff (g φ) p‖ ^ 2 ≤ c := by
      intro φ
      by_contra h
      exact hpX ⟨hp, hpN, φ, lt_of_not_ge h⟩
    let x : K := ⟨qCoeff f p, hRK (hR p hp hpN)⟩
    have hxint : IsIntegral ℤ x :=
      isIntegral_coe_intermediateField K x (isIntegral_of_mem R (hR p hp hpN))
    have hxB : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B := by
      intro φ
      rw [haK p hp hpN φ, hB_def]
      exact Real.le_sqrt_of_sq_le (hall φ)
    have hxF : x ∈ F := (Set.Finite.mem_toFinset (hs := _)).mpr ⟨hxint, hxB⟩
    exact Finset.mem_image.mpr ⟨x, hxF, rfl⟩

end DeligneSerre55

open CongruenceSubgroup
open scoped MatrixGroups

theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R) ∧
      ∀ η : ℝ, 0 < η → ∃ (Y : Finset ℂ) (X : Set ℕ),
        (∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
          ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
            (η + δ) * Real.log (1 / (s - 1))) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ X → ModularFormClass.qCoeff f p ∈ Y :=
  DeligneSerre55.main N ε f hf₁ hT

end S_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
end P2MW
export P2MW.S_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen (solution)
