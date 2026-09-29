-- Prove2me | solution 1 for DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/57b571b3-1e59-553c-952e-5c30fffa9d04

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Theorems.Thm_AutomorphicForm_exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable
import Theorems.Thm_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
p2m_attr_erase "instance" "Deep.NTSupply.instNormalRayClassSubgroup AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 HeckeIntegralSeam.finite_padicInt_quotient_span_p LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SpectralSide.instCompactSpaceMatrix instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient"
p2m_attr_erase "instance" "FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul"
p2m_attr_erase "simp" "LocalNewvector.coe_borelElem_inv FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"

set_option autoImplicit false

open CongruenceSubgroup IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped MatrixGroups

noncomputable section

namespace RankinWeightOneReduction

theorem prime_eq_of_natCast_mem_span {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : (p : 𝓞 ℚ) ∈ Ideal.span {(q : 𝓞 ℚ)}) : p = q := by
  have hdvd : (q : 𝓞 ℚ) ∣ (p : 𝓞 ℚ) := Ideal.mem_span_singleton.mp h
  have hdvd' : ((q : ℤ)) ∣ (p : ℤ) := by
    have := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hdvd
    simpa [map_natCast] using this
  have : q ∣ p := Int.natCast_dvd_natCast.mp hdvd'
  exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp this).symm

theorem prime_natCast_ringOfIntegers_rat {p : ℕ} (hp : p.Prime) : Prime (p : 𝓞 ℚ) := by
  have h1 : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) (p : ℤ) = (p : 𝓞 ℚ) := by
    simp [map_natCast]
  rw [← h2]
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ)).mpr h1

def primePlace (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {(p : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_natCast_ringOfIntegers_rat hp).ne_zero).mpr
    (prime_natCast_ringOfIntegers_rat hp)
  ne_bot := mt Ideal.span_singleton_eq_bot.mp (prime_natCast_ringOfIntegers_rat hp).ne_zero

theorem primePlace_asIdeal (p : ℕ) (hp : p.Prime) :
    (primePlace p hp).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := rfl

theorem absNorm_span_natCast_ringOfIntegers_rat (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
  rw [Ideal.absNorm_span_singleton]
  have : (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self]
  simp

def primeOf (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  (HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose

theorem primeOf_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (primeOf v).Prime :=
  (HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose_spec.1

theorem asIdeal_eq_span_primeOf (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {(primeOf v : 𝓞 ℚ)} :=
  (HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose_spec.2

theorem primeOf_eq_of_natCast_mem {v : HeightOneSpectrum (𝓞 ℚ)} {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 ℚ) ∈ v.asIdeal) : primeOf v = p := by
  rw [asIdeal_eq_span_primeOf] at h
  exact (prime_eq_of_natCast_mem_span hp (primeOf_prime v) h).symm

theorem primeOf_primePlace {p : ℕ} (hp : p.Prime) : primeOf (primePlace p hp) = p :=
  primeOf_eq_of_natCast_mem hp (Ideal.mem_span_singleton_self _)

theorem primePlace_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : primePlace p hp = primePlace q hq) : p = q := by
  have hmem : (p : 𝓞 ℚ) ∈ (primePlace q hq).asIdeal := h ▸ Ideal.mem_span_singleton_self _
  exact prime_eq_of_natCast_mem_span hp hq hmem

def placeOf (N : ℕ) (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) : HeightOneSpectrum (𝓞 ℚ) :=
  primePlace p.1 p.2.1

theorem placeOf_injective (N : ℕ) : Function.Injective (placeOf N) := fun p q hpq =>
  Subtype.ext (primePlace_inj p.2.1 q.2.1 hpq)

theorem primeOf_placeOf (N : ℕ) (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) :
    primeOf (placeOf N p) = (p : ℕ) :=
  primeOf_primePlace p.2.1

theorem absNorm_placeOf (N : ℕ) (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) :
    Ideal.absNorm (placeOf N p).asIdeal = (p : ℕ) :=
  absNorm_span_natCast_ringOfIntegers_rat p.1

theorem asIdeal_dvd_span_of_primeOf_dvd {v : HeightOneSpectrum (𝓞 ℚ)} {M : ℕ}
    (h : primeOf v ∣ M) : v.asIdeal ∣ Ideal.span {(M : 𝓞 ℚ)} := by
  rw [Ideal.dvd_span_singleton, asIdeal_eq_span_primeOf, Ideal.mem_span_singleton]
  exact Nat.cast_dvd_cast h

theorem norm_dirichletCharacter_apply_prime_eq_one {M : ℕ} (ψ : DirichletCharacter ℂ M)
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ M) : ‖ψ (p : ZMod M)‖ = 1 := by
  have hc : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr h
  have := ψ.unit_norm_eq_one (ZMod.unitOfCoprime p hc)
  simpa [ZMod.coe_unitOfCoprime] using this

def thetaOf {M : ℕ} (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1) :
    HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := top_ne_bot
  a := fun v => ModularFormClass.qCoeff g (primeOf v)
  b := fun v => ψ (primeOf v : ZMod M)

@[scoped simp] theorem thetaOf_a {M : ℕ} (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) : (thetaOf ψ g).a v = ModularFormClass.qCoeff g (primeOf v) :=
  rfl

@[scoped simp] theorem thetaOf_b {M : ℕ} (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) : (thetaOf ψ g).b v = ψ (primeOf v : ZMod M) :=
  rfl

theorem exists_agrees_isArithGenuineCuspRealizable_of_isPrimitiveForm
    {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 1)
    (hg : CuspForm.IsPrimitiveForm ψ g) :
    ∃ Θ' : HeckeEigensystem ℚ ℂ, Θ'.AgreesAwayFromFinite (thetaOf ψ g) ∧
      IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) Θ' := by
  have hΘ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M →
      ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
        ModularFormClass.qCoeff g p = (thetaOf ψ g).a v ∧ ψ (p : ZMod M) = (thetaOf ψ g).b v := by
    refine ⟨∅, fun p hp _ _ v hv => ?_⟩
    have h := primeOf_eq_of_natCast_mem hp hv
    simp [h]
  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
    SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  obtain ⟨Θ', hagree, R', hgen, -⟩ :=
    AutomorphicForm.exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
      (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov
      M ψ g hg (thetaOf ψ g) hΘ
  exact ⟨Θ', hagree, R', hgen⟩

theorem main
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → s < 2 →
      Summable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ N} =>
        ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) ∧
      ∑' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
        Real.log (1 / (s - 1)) + C := by
  classical

  obtain ⟨M, instM, ψ, g, -, hg, hgf⟩ :=
    CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen N 1 f hf₁ (fun p => ε (p : ZMod N)) hT

  obtain ⟨Θ', ⟨S₁, hS₁⟩, hreal⟩ :=
    exists_agrees_isArithGenuineCuspRealizable_of_isPrimitiveForm ψ g hg

  have hMne : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (NeZero.ne M)
  have hBfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {(M : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors hMne
  have hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ ∪ hBfin.toFinset → ‖Θ'.b v‖ = 1 := by
    intro v hv
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv
    rw [(hS₁ v hv.1).2, thetaOf_b]
    refine norm_dirichletCharacter_apply_prime_eq_one ψ (primeOf_prime v) fun hd => ?_
    exact hv.2 (asIdeal_dvd_span_of_primeOf_dvd hd)

  obtain ⟨C₀, hC₀⟩ :=
    AutomorphicForm.exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable
      Θ' hreal (S₁ ∪ hBfin.toFinset) hb

  set K : ℝ := ∑ v ∈ S₁, ‖ModularFormClass.qCoeff f (primeOf v)‖ ^ 2 with hK
  refine ⟨C₀ + K, fun s hs₁ hs₂ => ?_⟩
  obtain ⟨hsum, hle⟩ := hC₀ s hs₁ hs₂

  set G : HeightOneSpectrum (𝓞 ℚ) → ℝ :=
    fun v => ‖Θ'.a v‖ ^ 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)
  set H : HeightOneSpectrum (𝓞 ℚ) → ℝ :=
    fun v => if v ∈ S₁ then ‖ModularFormClass.qCoeff f (primeOf v)‖ ^ 2 else 0
  have hG0 : ∀ v, 0 ≤ G v := fun v =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hH_of_mem : ∀ v, v ∈ S₁ → H v = ‖ModularFormClass.qCoeff f (primeOf v)‖ ^ 2 :=
    fun v hv => if_pos hv
  have hH_of_not_mem : ∀ v, v ∉ S₁ → H v = 0 := fun v hv => if_neg hv
  have hH0 : ∀ v, 0 ≤ H v := fun v => by
    by_cases hv : v ∈ S₁
    · rw [hH_of_mem v hv]; exact sq_nonneg _
    · rw [hH_of_not_mem v hv]
  have hHsum : Summable H := summable_of_ne_finset_zero (s := S₁) hH_of_not_mem
  have hHtsum : ∑' v, H v = K := by
    rw [tsum_eq_sum (s := S₁) hH_of_not_mem, hK]
    exact Finset.sum_congr rfl hH_of_mem
  have hGsum : Summable G := hsum
  have hGle : ∑' v, G v ≤ Real.log (1 / (s - 1)) + C₀ := hle
  have hGH : Summable (fun v => G v + H v) := hGsum.add hHsum

  have hF_le : ∀ p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
      ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
        G (placeOf N p) + H (placeOf N p) := by
    intro p
    by_cases hp : placeOf N p ∈ S₁
    · have h1 : ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _)
          (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.1.one_lt.le)
            (by linarith))
      have h2 : H (placeOf N p) = ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 := by
        rw [hH_of_mem _ hp, primeOf_placeOf]
      linarith [hG0 (placeOf N p)]
    · have ha : Θ'.a (placeOf N p) = ModularFormClass.qCoeff f (p : ℕ) := by
        rw [(hS₁ _ hp).1, thetaOf_a, primeOf_placeOf]
        exact (hgf p.1 p.2.1 p.2.2).1
      have hn : (Ideal.absNorm (placeOf N p).asIdeal : ℝ) = ((p : ℕ) : ℝ) := by
        rw [absNorm_placeOf]
      have hG : G (placeOf N p) = ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) := by
        show ‖Θ'.a (placeOf N p)‖ ^ 2 * (Ideal.absNorm (placeOf N p).asIdeal : ℝ) ^ (-s) = _
        rw [ha, hn]
      rw [hH_of_not_mem _ hp, add_zero, hG]
  have hF0 : ∀ p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
      0 ≤ ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) := fun p =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hFsum : Summable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ N} =>
      ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) :=
    Summable.of_nonneg_of_le hF0 hF_le (hGH.comp_injective (placeOf_injective N))
  refine ⟨hFsum, ?_⟩
  calc ∑' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
        ≤ ∑' v, (G v + H v) :=
          Summable.tsum_le_tsum_of_inj (placeOf N) (placeOf_injective N)
            (fun c _ => add_nonneg (hG0 c) (hH0 c)) hF_le hFsum hGH
    _ = ∑' v, G v + ∑' v, H v := hGsum.tsum_add hHsum
    _ ≤ Real.log (1 / (s - 1)) + C₀ + K := by rw [hHtsum]; linarith
    _ = Real.log (1 / (s - 1)) + (C₀ + K) := by ring

end RankinWeightOneReduction
p2m_reactivate "P2MW.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen.RankinWeightOneReduction"

end
p2m_reactivate "P2MW.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen.RankinWeightOneReduction"

open CongruenceSubgroup
open scoped MatrixGroups

theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → s < 2 →
      Summable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ N} =>
        ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) ∧
      ∑' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
        Real.log (1 / (s - 1)) + C :=
  RankinWeightOneReduction.main N ε f hf₁ hT

end S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
end P2MW
export P2MW.S_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen (solution)
