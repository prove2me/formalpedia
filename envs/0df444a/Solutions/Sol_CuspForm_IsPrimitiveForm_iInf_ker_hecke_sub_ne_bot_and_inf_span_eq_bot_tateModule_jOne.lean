-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.iInf_ker_hecke_sub_ne_bot_and_inf_span_eq_bot_tateModule_jOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b9bb4838-6a25-5cc6-beb8-47902cc66d99

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule

import Theorems.Thm_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot
import Theorems.Thm_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good
import Theorems.Thm_ModularCurve_exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good
import Theorems.Thm_CuspForm_IsPrimitiveForm_exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Theorems.Thm_CuspForm_IsEigenformWith_fg_adjoin_qCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_iInf_ker_hecke_sub_ne_bot_and_inf_span_eq_bot_tateModule_jOne
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply"
p2m_attr_erase "simp" "CohCarrier.HeckeData.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coeffCoboundaryMap_apply Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false
open scoped TensorProduct

namespace K6Glue

theorem noZeroSMulDivisors_tateModule (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] :
    NoZeroSMulDivisors ℤ_[p] (TateModule p J) := by
  refine ⟨fun {a x} hax => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha (PadicInt.irreducible_p (p := p))
  have hpk : ((p : ℤ_[p]) ^ k) • x = 0 := by
    have := congrArg (fun y => ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • y) hax
    simp only [smul_zero] at this
    rwa [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  apply Subtype.ext
  funext n
  have h1 := TateModule.compat_pow x n k
  have h2 : (((((p ^ k : ℕ) : ℤ_[p])) • x : TateModule p J) : ℕ → J) (n + k) = 0 := by
    rw [Nat.cast_pow, hpk]; rfl
  rw [TateModule.natCast_padicInt_smul_apply] at h2
  rw [← h1, h2]
  rfl

theorem free_tateModule (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module.Finite ℤ_[p] (TateModule p J)] :
    Module.Free ℤ_[p] (TateModule p J) := by
  haveI := noZeroSMulDivisors_tateModule p J
  exact Module.free_of_finite_type_torsion_free'

theorem aeval_tateHeckeRepOne_eq_zero (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]
    [Module ModularCurve.HeckeAlgOne J] (w : ModularCurve.HeckeAlgOne) (P : Polynomial ℤ)
    (hP : ∀ x : J, (Polynomial.aeval w P : ModularCurve.HeckeAlgOne) • x = 0) :
    Polynomial.aeval (ModularCurve.tateHeckeRepOne p J w) P = 0 := by
  have h := Polynomial.aeval_algHom_apply (ModularCurve.tateHeckeRepOne p J).toIntAlgHom w P
  rw [RingHom.toIntAlgHom_apply, RingHom.toIntAlgHom_apply] at h
  rw [h]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  rw [ModularCurve.coe_tateHeckeRepOne_apply_apply, hP]
  rfl

theorem tateHeckeRepOne_mul_eq (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]
    [Module ModularCurve.HeckeAlgOne J] (s t u : ModularCurve.HeckeAlgOne) (hst : ∀ x : J, (s * t) • x = u • x) :
    ModularCurve.tateHeckeRepOne p J s * ModularCurve.tateHeckeRepOne p J t = ModularCurve.tateHeckeRepOne p J u := by
  rw [← map_mul]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  rw [ModularCurve.coe_tateHeckeRepOne_apply_apply, ModularCurve.coe_tateHeckeRepOne_apply_apply, hst]

theorem ringHom_apply_ne_zero_of_isIntegral {R K : Type*} [CommRing R] [IsDomain R] [Field K] [CharZero K]
    (ψ : R →+* K) {z : R} (hz : IsIntegral ℤ z) (hz0 : z ≠ 0) : ψ z ≠ 0 := by
  obtain ⟨P, hPmonic, hPz⟩ := hz
  have hP0 : P ≠ 0 := hPmonic.ne_zero

  set k := Polynomial.rootMultiplicity 0 P
  set P' := P /ₘ (Polynomial.X - Polynomial.C 0) ^ k with hP'
  have hfac : (Polynomial.X - Polynomial.C 0) ^ k * P' = P := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq P 0
  have hev : Polynomial.eval 0 P' ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hP0

  have hP'z : Polynomial.eval₂ (Int.castRingHom R) z P' = 0 := by
    have h := hPz
    rw [← hfac, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      map_zero, sub_zero] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (pow_eq_zero_iff'.mp h1).1 hz0
    · exact h1
  intro hψz
  apply hev
  have h2 : ψ (Polynomial.eval₂ (Int.castRingHom R) z P') = 0 := by rw [hP'z, map_zero]
  rw [Polynomial.hom_eval₂, hψz] at h2

  have h3 : Polynomial.eval₂ (ψ.comp (Int.castRingHom R)) (0 : K) P' = ((Polynomial.eval 0 P' : ℤ) : K) := by
    rw [show ψ.comp (Int.castRingHom R) = Int.castRingHom K from RingHom.ext_int _ _, Polynomial.eval₂_at_zero,
      Polynomial.coeff_zero_eq_eval_zero]
    rfl
  rw [h3] at h2
  exact_mod_cast h2

theorem G2_ne_zero {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg1 : CuspForm.IsEigenformWith ε g) (p : ℕ) [Fact p.Prime]
    (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    (S : Finset ℕ) (K : Type) [Field K] [CharZero K]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* K)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p J) →+* K)
    (hpkt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        Λ (ModularCurve.rationalHeckeOne p J ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧
        Λ (ModularCurve.rationalDiamondOne p J ℓ) * ψ (e ℓ) = 1)
    (s : ModularCurve.HeckeAlgOne)
    (hs : s ∈ Algebra.adjoin ℤ
        {x : ModularCurve.HeckeAlgOne |
          ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
            (x = ModularCurve.heckeGenOne ℓ ∨ x = ModularCurve.diamondGen (ℓ : ℕ))})
    (hθ : MvPolynomial.aeval
            (Sum.elim (fun ℓ : Nat.Primes => ModularFormClass.qCoeff g ℓ * (ε ((ℓ : ℕ) : ZMod M))⁻¹)
              (fun d : ℕ => (ε (d : ZMod M))⁻¹)) s ≠ 0) :
    Λ ⟨ModularCurve.rationalHeckeRepOne p J s, ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J s⟩ ≠ 0 := by
  classical
  haveI : IsDomain R := Function.Injective.isDomain toC htoC
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  let φM : ℕ := Nat.totient M
  have hφpos : 0 < φM := Nat.totient_pos.mpr hM0

  have hεpow : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ε (ℓ : ZMod M)) ^ φM = 1 := by
    intro ℓ hℓ hℓM
    have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM
    rw [← ZMod.coe_unitOfCoprime ℓ hcop, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  have hεne : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ε (ℓ : ZMod M) ≠ 0 := by
    intro ℓ hℓ hℓM h0
    have := hεpow ℓ hℓ hℓM
    rw [h0, zero_pow hφpos.ne'] at this
    exact zero_ne_one this
  have hεinv : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ε (ℓ : ZMod M)) ^ (φM - 1) = (ε (ℓ : ZMod M))⁻¹ := by
    intro ℓ hℓ hℓM
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hφpos, hεpow ℓ hℓ hℓM]
  have hepow : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → e ℓ ^ φM = 1 := by
    intro ℓ hℓ hℓM hℓS
    apply htoC
    rw [map_pow, he ℓ hℓ hℓM hℓS, hεpow ℓ hℓ hℓM, map_one]
  have hψe0 : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → ψ (e ℓ) ≠ 0 := by
    intro ℓ hℓ hℓM hℓS h0
    have := (hpkt ℓ hℓ hℓM hℓS).2
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hψeinv : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → ψ (e ℓ) ^ (φM - 1) = (ψ (e ℓ))⁻¹ := by
    intro ℓ hℓ hℓM hℓS
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hφpos, ← map_pow, hepow ℓ hℓ hℓM hℓS, map_one]

  let ν : Nat.Primes ⊕ ℕ → R := Sum.elim (fun ℓ => b ℓ * e ℓ ^ (φM - 1)) (fun d => e d ^ (φM - 1))
  let χ : ModularCurve.HeckeAlgOne →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) ν

  let Igood : Set (Nat.Primes ⊕ ℕ) := {i | ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧ (i = Sum.inl ℓ ∨ i = Sum.inr (ℓ : ℕ))}
  have hgoodset : {x : ModularCurve.HeckeAlgOne |
        ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
          (x = ModularCurve.heckeGenOne ℓ ∨ x = ModularCurve.diamondGen (ℓ : ℕ))} = MvPolynomial.X '' Igood := by
    ext x
    constructor
    · rintro ⟨ℓ, h1, h2, h3⟩
      rcases h3 with rfl | rfl
      · exact ⟨Sum.inl ℓ, ⟨ℓ, h1, h2, Or.inl rfl⟩, rfl⟩
      · exact ⟨Sum.inr (ℓ : ℕ), ⟨ℓ, h1, h2, Or.inr rfl⟩, rfl⟩
    · rintro ⟨i, ⟨ℓ, h1, h2, h3⟩, rfl⟩
      rcases h3 with rfl | rfl
      · exact ⟨ℓ, h1, h2, Or.inl rfl⟩
      · exact ⟨ℓ, h1, h2, Or.inr rfl⟩
  have hvars : ∀ i ∈ s.vars, i ∈ Igood := by
    have hs' : s ∈ MvPolynomial.supported ℤ Igood := by
      rw [MvPolynomial.supported_eq_adjoin_X, ← hgoodset]; exact hs
    rw [MvPolynomial.mem_supported] at hs'
    exact fun i hi => hs' hi

  have hA : toC (χ s) = MvPolynomial.aeval
      (Sum.elim (fun ℓ : Nat.Primes => ModularFormClass.qCoeff g ℓ * (ε ((ℓ : ℕ) : ZMod M))⁻¹)
        (fun d : ℕ => (ε (d : ZMod M))⁻¹)) s := by
    show (toC.comp χ) s = (MvPolynomial.aeval _ : ModularCurve.HeckeAlgOne →ₐ[ℤ] ℂ).toRingHom s
    apply MvPolynomial.hom_congr_vars _ _ rfl
    · exact RingHom.ext_int _ _
    · intro i hi _
      obtain ⟨ℓ, h1, h2, h3⟩ := hvars i hi
      rcases h3 with rfl | rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
          Sum.elim_inl]
        show toC (MvPolynomial.eval₂ (Int.castRingHom R) ν (MvPolynomial.X (Sum.inl ℓ))) = _
        rw [MvPolynomial.eval₂_X]
        show toC (b ℓ * e ℓ ^ (φM - 1)) = _
        rw [map_mul, map_pow, hb ℓ ℓ.2 h1 h2, he ℓ ℓ.2 h1 h2, hεinv ℓ ℓ.2 h1]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
          Sum.elim_inr]
        show toC (MvPolynomial.eval₂ (Int.castRingHom R) ν (MvPolynomial.X (Sum.inr (ℓ : ℕ)))) = _
        rw [MvPolynomial.eval₂_X]
        show toC (e ℓ ^ (φM - 1)) = _
        rw [map_pow, he ℓ ℓ.2 h1 h2, hεinv ℓ ℓ.2 h1]

  let lamT : ModularCurve.HeckeAlgOne →+* K :=
    Λ.comp ((ModularCurve.rationalHeckeRepOne p (J)).codRestrict
      (ModularCurve.rationalHeckeAlgebraOne p (J)).toSubring.toSubsemiring
      (ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p (J)))
  have hB : ψ (χ s) = lamT s := by
    show (ψ.comp χ) s = lamT s
    apply MvPolynomial.hom_congr_vars _ _ rfl
    · exact RingHom.ext_int _ _
    · intro i hi _
      obtain ⟨ℓ, h1, h2, h3⟩ := hvars i hi
      obtain ⟨hT, hD⟩ := hpkt ℓ ℓ.2 h1 h2
      rcases h3 with rfl | rfl
      · show ψ (MvPolynomial.eval₂ (Int.castRingHom R) ν (MvPolynomial.X (Sum.inl ℓ))) =
          Λ (ModularCurve.rationalHeckeOne p (J) ℓ)
        rw [MvPolynomial.eval₂_X]
        show ψ (b ℓ * e ℓ ^ (φM - 1)) = _
        rw [map_mul, map_pow, hψeinv ℓ ℓ.2 h1 h2, ← hT, mul_assoc, mul_inv_cancel₀ (hψe0 ℓ ℓ.2 h1 h2), mul_one]
        rfl
      · show ψ (MvPolynomial.eval₂ (Int.castRingHom R) ν (MvPolynomial.X (Sum.inr (ℓ : ℕ)))) =
          Λ (ModularCurve.rationalDiamondOne p (J) ℓ)
        rw [MvPolynomial.eval₂_X]
        show ψ (e ℓ ^ (φM - 1)) = _
        rw [map_pow, hψeinv ℓ ℓ.2 h1 h2]
        exact (eq_inv_of_mul_eq_one_left hD).symm

  have hχ0 : χ s ≠ 0 := by
    intro h0; apply hθ; rw [← hA, h0, map_zero]
  have hint : IsIntegral ℤ (χ s) := by

    have hfg := CuspForm.IsEigenformWith.fg_adjoin_qCoeff hg1
    set Ag := Algebra.adjoin ℤ ((Set.range fun n : ℕ => ModularFormClass.qCoeff g n) ∪
      Set.range fun u : (ZMod M)ˣ => ε (u : ZMod M)) with hAg
    have hbint : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsIntegral ℤ (b ℓ) := by
      intro ℓ hℓ hℓM hℓS
      have h1 : IsIntegral ℤ (toC (b ℓ)) := by
        rw [hb ℓ hℓ hℓM hℓS]
        exact IsIntegral.of_mem_of_fg Ag hfg _ (Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩))
      exact (isIntegral_algHom_iff toC.toIntAlgHom htoC).mp h1
    have heint : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsIntegral ℤ (e ℓ) := by
      intro ℓ hℓ hℓM hℓS
      have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM
      have h1 : IsIntegral ℤ (toC (e ℓ)) := by
        rw [he ℓ hℓ hℓM hℓS]
        refine IsIntegral.of_mem_of_fg Ag hfg _ (Algebra.subset_adjoin (Or.inr ⟨ZMod.unitOfCoprime ℓ hcop, ?_⟩))
        show ε ((ZMod.unitOfCoprime ℓ hcop : (ZMod M)ˣ) : ZMod M) = ε (ℓ : ZMod M)
        rw [ZMod.coe_unitOfCoprime]
      exact (isIntegral_algHom_iff toC.toIntAlgHom htoC).mp h1
    have hνint : ∀ i ∈ Igood, IsIntegral ℤ (ν i) := by
      rintro i ⟨ℓ, h1, h2, h3⟩
      rcases h3 with rfl | rfl
      · exact (hbint ℓ ℓ.2 h1 h2).mul ((heint ℓ ℓ.2 h1 h2).pow _)
      · exact (heint ℓ ℓ.2 h1 h2).pow _

    have hmem : χ s ∈ Algebra.adjoin ℤ (ν '' Igood) := by
      have hs' : s ∈ MvPolynomial.supported ℤ Igood := by
        rw [MvPolynomial.supported_eq_adjoin_X, ← hgoodset]; exact hs
      rw [MvPolynomial.supported_eq_range_rename, AlgHom.mem_range] at hs'
      obtain ⟨s', rfl⟩ := hs'
      show MvPolynomial.eval₂ (Int.castRingHom R) ν (MvPolynomial.rename ((↑) : Igood → Nat.Primes ⊕ ℕ) s') ∈ _
      rw [MvPolynomial.eval₂_rename]
      apply MvPolynomial.eval₂_mem
      · intro d _
        show ((Int.castRingHom R) (MvPolynomial.coeff d s')) ∈ Algebra.adjoin ℤ (ν '' Igood)
        rw [eq_intCast]
        exact Subalgebra.intCast_mem _ _
      · intro i
        exact Algebra.subset_adjoin ⟨i, i.2, rfl⟩
    have hle : Algebra.adjoin ℤ (ν '' Igood) ≤ integralClosure ℤ R := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, hi, rfl⟩
      exact hνint i hi
    exact hle hmem
  show lamT s ≠ 0
  rw [← hB]
  exact K6Glue.ringHom_apply_ne_zero_of_isIntegral ψ hint hχ0

end K6Glue

theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (S : Finset ℕ) (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* K)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* K,
      (∀ c : ℤ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M))
            (c : ℚ_[p]))
          = algebraMap ℤ_[p] K c) →
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧
        Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * ψ (e ℓ) = 1) →
      (⨅ t : ModularCurve.HeckeAlgOne,
          LinearMap.ker
            ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K -
              Λ ⟨ModularCurve.rationalHeckeRepOne p (ModularCurve.JOne M) t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p
                    (ModularCurve.JOne M) t⟩ • LinearMap.id)) ≠ ⊥ ∧
      (⨅ t : ModularCurve.HeckeAlgOne,
          LinearMap.ker
            ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K -
              Λ ⟨ModularCurve.rationalHeckeRepOne p (ModularCurve.JOne M) t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p
                    (ModularCurve.JOne M) t⟩ • LinearMap.id)) ⊓
        Submodule.span K
          {z : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M) |
            ∃ (t : ModularCurve.HeckeAlgOne) (y : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
              z = (ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K y -
                Λ ⟨ModularCurve.rationalHeckeRepOne p (ModularCurve.JOne M) t,
                    ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p
                      (ModularCurve.JOne M) t⟩ • y} = ⊥ := by
  letI := ModularCurve.heckeModuleOneBar M
  refine fun Λ hΛ hpkt => ?_

  haveI hfin : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JOne M)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jOne M p
  haveI hfree : Module.Free ℤ_[p] (TateModule p (ModularCurve.JOne M)) := K6Glue.free_tateModule p _
  refine ⟨ModularCurve.iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot p (ModularCurve.JOne M) K Λ hΛ, ?_⟩
  refine ModularCurve.iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good p (ModularCurve.JOne M) K Λ hΛ
    {x : ModularCurve.HeckeAlgOne |
      ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
        (x = ModularCurve.heckeGenOne ℓ ∨ x = ModularCurve.diamondGen (ℓ : ℕ))} ?_ ?_
  ·
    intro w hw
    obtain ⟨P, hP0, hPsep, hPann⟩ :=
      ModularCurve.exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good M hin hcomm S w hw
    exact ⟨P, hP0, hPsep, K6Glue.aeval_tateHeckeRepOne_eq_zero p _ w P hPann⟩
  ·
    have h2 := CuspForm.IsPrimitiveForm.exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne hg hin hcomm S
    intro t
    have h3 := h2 t
    rcases h3 with ⟨s, hs, h4⟩
    rcases h4 with ⟨u, hu, h5⟩
    obtain ⟨hθ, hst⟩ := h5
    refine ⟨s, hs, u, hu, ?_, K6Glue.tateHeckeRepOne_mul_eq p _ s t u hst⟩

    exact K6Glue.G2_ne_zero hg.1 p _ S K R toC htoC ψ b e hb he Λ hpkt s hs hθ

end S_CuspForm_IsPrimitiveForm_iInf_ker_hecke_sub_ne_bot_and_inf_span_eq_bot_tateModule_jOne
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_iInf_ker_hecke_sub_ne_bot_and_inf_span_eq_bot_tateModule_jOne (solution)
