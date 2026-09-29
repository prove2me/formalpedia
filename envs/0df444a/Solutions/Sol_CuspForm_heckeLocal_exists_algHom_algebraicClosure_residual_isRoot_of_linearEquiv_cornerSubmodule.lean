-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_algHom_algebraicClosure_residual_isRoot_of_linearEquiv_cornerSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/42e12d83-047f-5f3a-86c9-32e1e5eaa223

import Mathlib
import Definitions.Def_CuspForm_HeckeModuleCornerRealization
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_CuspForm_Newforms
import Theorems.Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
import Theorems.Thm_CohCarrier_exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms
import Theorems.Thm_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_algHom_algebraicClosure_residual_isRoot_of_linearEquiv_cornerSubmodule
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex CuspForm.GammaH_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away"
p2m_attr_erase "simp" "Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open Polynomial IsLocalRing
open scoped TensorProduct IsMulCommutative

namespace OCC

theorem commute_baseChange {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] {f g : Module.End R M} (h : Commute f g) :
    Commute (f.baseChange A) (g.baseChange A) := by
  have h' : f ∘ₗ g = g ∘ₗ f := by
    have := h.eq
    rwa [Module.End.mul_eq_comp, Module.End.mul_eq_comp] at this
  show f.baseChange A * g.baseChange A = g.baseChange A * f.baseChange A
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.baseChange_comp,
    ← LinearMap.baseChange_comp, h']

theorem exists_algHom_eigenvector
    {𝒪 : Type*} [CommRing 𝒪] (K : Type*) [Field K] [IsAlgClosed K] [Algebra 𝒪 K]
    {T : Type*} [CommRing T] [Algebra 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M] [Module.Finite 𝒪 M]
    {ι : Type*} (c : ι → Module.End 𝒪 M)
    (hcc : ∀ i j, Commute (c i) (c j))
    (hct : ∀ (i : ι) (t : T) (m : M), c i (t • m) = t • c i m)
    [Nontrivial (K ⊗[𝒪] M)] :
    ∃ (χ : T →ₐ[𝒪] K) (a : ι → K) (v : K ⊗[𝒪] M), v ≠ 0 ∧
      (∀ t : T, ((LinearMap.lsmul T M t).restrictScalars 𝒪).baseChange K v = χ t • v) ∧
      (∀ i, (c i).baseChange K v = a i • v) := by
  classical
  let ρ : T → Module.End 𝒪 M := fun t => (LinearMap.lsmul T M t).restrictScalars 𝒪
  have hρ_apply : ∀ t m, ρ t m = t • m := fun t m => rfl
  have hρ_one : ρ 1 = LinearMap.id := by
    apply LinearMap.ext; intro m; rw [hρ_apply, one_smul, LinearMap.id_apply]
  have hρ_mul : ∀ s t, ρ (s * t) = ρ s ∘ₗ ρ t := by
    intro s t; apply LinearMap.ext; intro m
    rw [LinearMap.comp_apply, hρ_apply, hρ_apply, hρ_apply, mul_smul]
  have hρ_add : ∀ s t, ρ (s + t) = ρ s + ρ t := by
    intro s t; apply LinearMap.ext; intro m
    rw [LinearMap.add_apply, hρ_apply, hρ_apply, hρ_apply, add_smul]
  have hρ_zero : ρ 0 = 0 := by
    apply LinearMap.ext; intro m; rw [hρ_apply, zero_smul, LinearMap.zero_apply]
  have hρ_alg : ∀ r : 𝒪, ρ (algebraMap 𝒪 T r) = r • LinearMap.id := by
    intro r; apply LinearMap.ext; intro m
    rw [hρ_apply, algebraMap_smul, LinearMap.smul_apply, LinearMap.id_apply]
  have hρc : ∀ t i, Commute (ρ t) (c i) := by
    intro t i; apply LinearMap.ext; intro m
    show ρ t (c i m) = c i (ρ t m)
    rw [hρ_apply, hρ_apply, hct]
  have hρρ : ∀ s t, Commute (ρ s) (ρ t) := by
    intro s t
    show ρ s * ρ t = ρ t * ρ s
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← hρ_mul, ← hρ_mul, mul_comm]

  let F : T ⊕ ι → Module.End K (K ⊗[𝒪] M) :=
    Sum.elim (fun t => (ρ t).baseChange K) (fun i => (c i).baseChange K)
  have hF : Pairwise fun x y => Commute (F x) (F y) := by
    intro x y _
    rcases x with t | i <;> rcases y with s | j
    · exact commute_baseChange (hρρ t s)
    · exact commute_baseChange (hρc t j)
    · exact commute_baseChange (hρc s i).symm
    · exact commute_baseChange (hcc i j)
  obtain ⟨v, hv, hev⟩ := Module.End.exists_forall_apply_eq_smul_of_pairwise_commute F hF
  choose ev hev using hev
  have hinj : ∀ a b : K, a • v = b • v → a = b := fun a b h => smul_left_injective K hv h
  have hevl : ∀ t, (ρ t).baseChange K v = ev (Sum.inl t) • v := fun t => hev (Sum.inl t)
  have h_one : ev (Sum.inl 1) = 1 := by
    apply hinj
    rw [← hevl, hρ_one, LinearMap.baseChange_id, one_smul, LinearMap.id_apply]
  have h_mul : ∀ s t, ev (Sum.inl (s * t)) = ev (Sum.inl s) * ev (Sum.inl t) := by
    intro s t
    apply hinj
    rw [← hevl, hρ_mul, LinearMap.baseChange_comp, LinearMap.comp_apply, hevl t, map_smul, hevl s,
      smul_smul, mul_comm]
  have h_zero : ev (Sum.inl 0) = 0 := by
    apply hinj
    rw [← hevl, hρ_zero, LinearMap.baseChange_zero, zero_smul, LinearMap.zero_apply]
  have h_add : ∀ s t, ev (Sum.inl (s + t)) = ev (Sum.inl s) + ev (Sum.inl t) := by
    intro s t
    apply hinj
    rw [← hevl, hρ_add, LinearMap.baseChange_add, LinearMap.add_apply, hevl, hevl, add_smul]
  have h_alg : ∀ r : 𝒪, ev (Sum.inl (algebraMap 𝒪 T r)) = algebraMap 𝒪 K r := by
    intro r
    apply hinj
    rw [← hevl, hρ_alg, LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.baseChange_id,
      LinearMap.id_apply, algebraMap_smul]
  let χ : T →ₐ[𝒪] K :=
    { toFun := fun t => ev (Sum.inl t)
      map_one' := h_one
      map_mul' := h_mul
      map_zero' := h_zero
      map_add' := h_add
      commutes' := h_alg }
  exact ⟨χ, fun i => ev (Sum.inr i), v, hv, fun t => hev (Sum.inl t), fun i => hev (Sum.inr i)⟩

end OCC

namespace OCC

section Act
variable {𝒪 T M : Type*} [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T] [AddCommGroup M] [Module T M]
  [Module 𝒪 M] [IsScalarTower 𝒪 T M]

theorem act_apply (t : T) (m : M) : (LinearMap.lsmul T M t).restrictScalars 𝒪 m = t • m := rfl

theorem act_one : (LinearMap.lsmul T M 1).restrictScalars 𝒪 = (1 : Module.End 𝒪 M) := by
  apply LinearMap.ext; intro m; rw [act_apply, one_smul, Module.End.one_apply]

theorem act_mul (s t : T) : (LinearMap.lsmul T M (s * t)).restrictScalars 𝒪 =
    (LinearMap.lsmul T M s).restrictScalars 𝒪 * (LinearMap.lsmul T M t).restrictScalars 𝒪 := by
  apply LinearMap.ext; intro m; rw [Module.End.mul_apply, act_apply, act_apply, act_apply, mul_smul]

theorem act_add (s t : T) : (LinearMap.lsmul T M (s + t)).restrictScalars 𝒪 =
    (LinearMap.lsmul T M s).restrictScalars 𝒪 + (LinearMap.lsmul T M t).restrictScalars 𝒪 := by
  apply LinearMap.ext; intro m; rw [LinearMap.add_apply, act_apply, act_apply, act_apply, add_smul]

theorem act_zero : (LinearMap.lsmul T M 0).restrictScalars 𝒪 = (0 : Module.End 𝒪 M) := by
  apply LinearMap.ext; intro m; rw [act_apply, zero_smul, LinearMap.zero_apply]

theorem act_algebraMap (r : 𝒪) :
    (LinearMap.lsmul T M (algebraMap 𝒪 T r)).restrictScalars 𝒪 = r • (1 : Module.End 𝒪 M) := by
  apply LinearMap.ext; intro m
  rw [act_apply, algebraMap_smul, LinearMap.smul_apply, Module.End.one_apply]

end Act

section H1
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]

scoped instance noZeroSMulDivisors_H1 (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    NoZeroSMulDivisors 𝒪 (CohCarrier.H1 N H 𝒪) := by
  refine ⟨fun {r φ} h => ?_⟩
  by_cases hr : r = 0
  · exact Or.inl hr
  · refine Or.inr (AddMonoidHom.ext fun x => ?_)
    have hx : r * φ x = 0 := by
      have := DFunLike.congr_fun h x
      simpa only [AddMonoidHom.smul_apply, smul_eq_mul, AddMonoidHom.zero_apply] using this
    rw [AddMonoidHom.zero_apply]
    exact (mul_eq_zero.mp hx).resolve_left hr

theorem free_H1 [IsDiscreteValuationRing 𝒪] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    Module.Free 𝒪 (CohCarrier.H1 N H 𝒪) := by
  haveI : Module.Finite 𝒪 (CohCarrier.H1 N H 𝒪) := CohCarrier.H1_moduleFinite N H 𝒪 𝒪
  exact Module.free_of_finite_type_torsion_free'

end H1

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem exists_corner_action
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M]
    (eM : M ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)))
    (hequiv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) (m : M),
      ((eM (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) • m) :
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 N ⊤ 𝒪) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          CohCarrier.heckeT N ⊤ ℓ 𝒪
            ((eM m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 N ⊤ 𝒪))) :
    ∃ cg : ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra → Module.End 𝒪 M,
      (∀ (b : ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra) (m : M),
        ((eM (cg b m) : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) :
            CohCarrier.H1 N ⊤ 𝒪) =
          (b : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪))
            ((eM m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 N ⊤ 𝒪)) ∧
      (∀ b b' : ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra,
        cg b * cg b' = cg b' * cg b) ∧
      (∀ (b : ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
        (t : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) (m : M), cg b (t • m) = t • cg b m) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
        (LinearMap.lsmul (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ
          (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))).restrictScalars 𝒪 =
        cg ⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN),
          Algebra.subset_adjoin (Set.mem_range_self _)⟩) := by
  classical
  let Tθ : Type := CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ
  let H : Type := CohCarrier.H1 N ⊤ 𝒪
  let D := CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar
  let Cor := IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)
  let bg : CohCarrier.Gen N (↑S : Set ℕ) → ↥D.opSubalgebra := fun g =>
    ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
  let cg : ↥D.opSubalgebra → Module.End 𝒪 M := fun b =>
    eM.symm.toLinearMap ∘ₗ
      (({ toFun := fun x => ⟨(b : Module.End 𝒪 H) (x : H), Cor.smul_mem b x.2⟩
          map_add' := fun x y => Subtype.ext (map_add (b : Module.End 𝒪 H) (x : H) (y : H))
          map_smul' := fun r x => Subtype.ext (map_smul (b : Module.End 𝒪 H) r (x : H)) } :
          ↥Cor →ₗ[𝒪] ↥Cor) ∘ₗ eM.toLinearMap)
  have hcg_coe : ∀ (b : ↥D.opSubalgebra) (m : M),
      ((eM (cg b m) : ↥Cor) : H) = (b : Module.End 𝒪 H) ((eM m : ↥Cor) : H) :=
    fun b m => congrArg Subtype.val (eM.apply_symm_apply _)
  have hcg_mul : ∀ b b' : ↥D.opSubalgebra, cg (b * b') = cg b * cg b' := by
    intro b b'
    apply LinearMap.ext; intro m; apply eM.injective; apply Subtype.ext
    simp only [hcg_coe, Module.End.mul_apply, Subalgebra.coe_mul]
  have hcg_comm : ∀ b b' : ↥D.opSubalgebra, cg b * cg b' = cg b' * cg b := by
    intro b b'
    rw [← hcg_mul, ← hcg_mul, mul_comm]
  have hcg_one : cg 1 = 1 := by
    apply LinearMap.ext; intro m; apply eM.injective; apply Subtype.ext
    simp only [hcg_coe, Module.End.one_apply, Subalgebra.coe_one]
  have hcg_add : ∀ b b' : ↥D.opSubalgebra, cg (b + b') = cg b + cg b' := by
    intro b b'
    apply LinearMap.ext; intro m; apply eM.injective; apply Subtype.ext
    simp only [hcg_coe, LinearMap.add_apply, Subalgebra.coe_add, map_add, Submodule.coe_add]
  have hcg_zero : cg 0 = 0 := by
    apply LinearMap.ext; intro m; apply eM.injective; apply Subtype.ext
    simp only [hcg_coe, LinearMap.zero_apply, ZeroMemClass.coe_zero, map_zero]
  have hcg_alg : ∀ r : 𝒪, cg (algebraMap 𝒪 (↥D.opSubalgebra) r) = r • (1 : Module.End 𝒪 M) := by
    intro r
    apply LinearMap.ext; intro m; apply eM.injective; apply Subtype.ext
    simp only [hcg_coe, LinearMap.smul_apply, Module.End.one_apply, Subalgebra.coe_algebraMap,
      map_smul, Submodule.coe_smul_of_tower, Module.algebraMap_end_apply]

  have hF2 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      (LinearMap.lsmul Tθ M (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ
        (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))).restrictScalars 𝒪 =
      cg (bg (CohCarrier.Gen.T ℓ hℓ hℓS hℓN)) := by
    intro ℓ hℓ hℓS hℓN
    apply LinearMap.ext; intro m
    apply eM.injective
    apply Subtype.ext
    rw [OCC.act_apply, hequiv ℓ hℓ hℓS hℓN m]
    show _ = ((eM (cg (bg (CohCarrier.Gen.T ℓ hℓ hℓS hℓN)) m) : ↥Cor) : H)
    rw [hcg_coe]
    rfl

  let St : Subalgebra 𝒪 Tθ :=
    { carrier := {t | ∃ b : ↥D.opSubalgebra, (LinearMap.lsmul Tθ M t).restrictScalars 𝒪 = cg b}
      mul_mem' := fun {s t} hs ht => by
        obtain ⟨b, hb⟩ := hs
        obtain ⟨b', hb'⟩ := ht
        exact ⟨b * b', by rw [OCC.act_mul, hb, hb', hcg_mul]⟩
      one_mem' := ⟨1, by rw [OCC.act_one, hcg_one]⟩
      add_mem' := fun {s t} hs ht => by
        obtain ⟨b, hb⟩ := hs
        obtain ⟨b', hb'⟩ := ht
        exact ⟨b + b', by rw [OCC.act_add, hb, hb', hcg_add]⟩
      zero_mem' := ⟨0, by rw [OCC.act_zero, hcg_zero]⟩
      algebraMap_mem' := fun r => ⟨algebraMap 𝒪 _ r, by rw [OCC.act_algebraMap, hcg_alg]⟩ }
  have hgen : Set.range (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ) ⊆ (St : Set Tθ) := by
    rintro _ ⟨h, rfl⟩
    obtain ⟨h, hh⟩ := h
    induction hh using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
      · exact ⟨bg (CohCarrier.Gen.T ℓ hℓ hℓS hℓN), hF2 ℓ hℓ hℓS hℓN⟩
      · exact absurd (hNS q hq hqN) hqS
    | algebraMap n =>
      have : (⟨algebraMap ℤ _ n, Subalgebra.algebraMap_mem _ n⟩ :
          CuspForm.heckeAlgebra N 2 (↑S : Set ℕ)) = algebraMap ℤ (CuspForm.heckeAlgebra N 2 (↑S : Set ℕ)) n := rfl
      rw [this, eq_intCast, map_intCast]
      exact intCast_mem St n
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ)) =
          ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ).map_add]
      exact St.add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ)) =
          ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ).map_mul]
      exact St.mul_mem ihx ihy
  have hall : ∀ t : Tθ, ∃ b : ↥D.opSubalgebra, (LinearMap.lsmul Tθ M t).restrictScalars 𝒪 = cg b := by
    intro t
    have hadj := CuspForm.heckeLocal.adjoin_range_pi N (↑S : Set ℕ) 𝒪 θ Fact.out
    have ht : t ∈ Algebra.adjoin 𝒪 (Set.range (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ)) := by
      rw [hadj]; exact Algebra.mem_top
    exact Algebra.adjoin_le hgen ht
  have hct : ∀ (b : ↥D.opSubalgebra) (t : Tθ) (m : M), cg b (t • m) = t • cg b m := by
    intro b t m
    obtain ⟨b', hb'⟩ := hall t
    have e1 : t • m = cg b' m := by rw [← OCC.act_apply (𝒪 := 𝒪) t m, hb']
    have e2 : t • cg b m = cg b' (cg b m) := by rw [← OCC.act_apply (𝒪 := 𝒪) t (cg b m), hb']
    rw [e1, e2]
    exact congrArg (fun f : Module.End 𝒪 M => f m) (hcg_comm b b')
  exact ⟨cg, hcg_coe, hcg_comm, hct, hF2⟩

end OCC
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_exists_algHom_algebraicClosure_residual_isRoot_of_linearEquiv_cornerSubmodule.OCC"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
open scoped Classical in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (N : ℕ) [NeZero N]
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNp : ¬ p ^ 2 ∣ N)
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hNunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ N → q ^ 2 ∣ N)
    (hN3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ N)
    [Fact (CuspForm.HasIntegralStructure N 2)]

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N (↑S : Set ℕ), πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hpar : ∀ v : CohCarrier.H1 N ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ N) (hℓN : ¬ ℓ ∣ N),
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓL) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))

    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M]
    (eM : M ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)))
    (hequiv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) (m : M),
      ((eM (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) • m) :
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 N ⊤ 𝒪) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          CohCarrier.heckeT N ⊤ ℓ 𝒪
            ((eM m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 N ⊤ 𝒪))) :
    ∃ (χ₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪)) (a₀ : ℕ → AlgebraicClosure (FractionRing 𝒪)),
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
        (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a₀ q) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q hq hqN))) ^ R.natDegree) ∧
        ∀ (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
          (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (_ : g.IsNewform)
          (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
          (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
            chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
          (_ : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg),
            chig (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = ModularFormClass.qCoeff g q)
          (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪))
          (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN))
              (Set.notMem_empty ℓ))) = χ₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))),
          Polynomial.IsRoot
            (if hqP : Nat.Prime q then
              (let aq : AlgebraicClosure (FractionRing 𝒪) := if hqMg : q ∣ Mg
                  then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hqP hqMg (Set.notMem_empty q)))
                  else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hqP hqMg (Set.notMem_empty q)))
               let e : ℕ := N.factorization q - Mg.factorization q
               if e = 0 then X - C aq
               else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : AlgebraicClosure (FractionRing 𝒪)) else (q : AlgebraicClosure (FractionRing 𝒪)))))
             else 1) (a₀ q) := by
  classical

  let K : Type := AlgebraicClosure (FractionRing 𝒪)
  let Tθ : Type := CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ
  let H : Type := CohCarrier.H1 N ⊤ 𝒪
  let D := CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar
  let Cor := IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)
  have hinj : Function.Injective (algebraMap 𝒪 K) := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (FractionRing 𝒪) K]
    exact (algebraMap (FractionRing 𝒪) K).injective.comp (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  haveI hHfin : Module.Finite 𝒪 H := CohCarrier.H1_moduleFinite N ⊤ 𝒪 𝒪
  haveI hHfree : Module.Free 𝒪 H := OCC.free_H1 N ⊤

  let bg : CohCarrier.Gen N (↑S : Set ℕ) → ↥D.opSubalgebra := fun g =>
    ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
  obtain ⟨cg, hcg_coe, hcg_comm, hct, hF2⟩ :=
    OCC.exists_corner_action N S hNS θ hcomm θbar Sp i₀ M eM hequiv

  let jH : M →ₗ[𝒪] H := (Cor.subtype.restrictScalars 𝒪) ∘ₗ eM.toLinearMap
  have hjH_apply : ∀ m : M, jH m = ((eM m : ↥Cor) : H) := fun m => rfl
  have hjinj : Function.Injective jH := fun x y hxy => eM.injective (Subtype.ext hxy)
  haveI hMfin : Module.Finite 𝒪 M := Module.Finite.of_injective jH hjinj
  let pr : H →ₗ[𝒪] M :=
    eM.symm.toLinearMap ∘ₗ ((IharaLemma.toCorner (M := H) (Sp.e i₀)).restrictScalars 𝒪)
  have hprj : pr ∘ₗ jH = LinearMap.id := by
    apply LinearMap.ext; intro m
    show eM.symm (IharaLemma.toCorner (M := H) (Sp.e i₀) ((eM m : ↥Cor) : H)) = m
    have : IharaLemma.toCorner (M := H) (Sp.e i₀) ((eM m : ↥Cor) : H) = eM m :=
      Subtype.ext (Sp.e_smul_coe i₀ (eM m))
    rw [this, LinearEquiv.symm_apply_apply]
  have hwinj : Function.Injective (jH.baseChange K) := by
    intro x y hxy
    have := congrArg (pr.baseChange K) hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hprj,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this

  have hpush : ∀ b : ↥D.opSubalgebra, jH ∘ₗ cg b = (b : Module.End 𝒪 H) ∘ₗ jH := by
    intro b
    apply LinearMap.ext; intro m
    exact hcg_coe b m

  obtain ⟨Φ, hΦtmul, hΦT, hΦpar⟩ :=
    CohCarrier.exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms
      K hinj N ⊤

  have he0 : Sp.e i₀ ≠ 0 := by
    intro h
    apply Sp.notMem i₀
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : H, (Sp.e i₀ : Module.End 𝒪 H) h₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact he0 (Subtype.ext (LinearMap.ext hcon))
  let m₀ : M := eM.symm (IharaLemma.toCorner (M := H) (Sp.e i₀) h₀)
  have hjm₀ : jH m₀ ≠ 0 := by
    rw [hjH_apply, LinearEquiv.apply_symm_apply]
    exact hh₀
  haveI : Nontrivial (K ⊗[𝒪] M) := by
    refine nontrivial_of_ne ((1 : K) ⊗ₜ[𝒪] m₀) 0 fun h0 => ?_
    have h1 : (jH.baseChange K) ((1 : K) ⊗ₜ[𝒪] m₀) = 0 := by rw [h0, map_zero]
    rw [LinearMap.baseChange_tmul] at h1
    have h2 := congrArg Φ h1
    rw [map_zero, hΦtmul, one_smul] at h2
    apply hjm₀
    apply AddMonoidHom.ext
    intro γ
    have h3 := DFunLike.congr_fun h2 γ
    simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      AddMonoidHom.zero_apply] at h3
    rw [AddMonoidHom.zero_apply]
    exact (map_eq_zero_iff (algebraMap 𝒪 K) hinj).mp h3

  obtain ⟨χ₀, a, v, hv0, hvT, hvc⟩ :=
    OCC.exists_algHom_eigenvector K (T := Tθ) (M := M) cg (fun b b' => hcg_comm b b') hct
  have hvinj : ∀ x y : K, x • v = y • v → x = y := fun x y h => smul_left_injective K hv0 h

  let w : K ⊗[𝒪] H := jH.baseChange K v
  have hw0 : w ≠ 0 := fun h => hv0 (hwinj (h.trans (map_zero _).symm))
  have hwop : ∀ g : CohCarrier.Gen N (↑S : Set ℕ), (D.op g).baseChange K w = a (bg g) • w := by
    intro g
    show ((bg g : Module.End 𝒪 H).baseChange K) (jH.baseChange K v) = a (bg g) • jH.baseChange K v
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← hpush, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hvc, map_smul]
  have hwrange : w ∈ LinearMap.range ((Cor.subtype.restrictScalars 𝒪).baseChange K) :=
    ⟨(eM.toLinearMap).baseChange K v, by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]⟩
  have hwpar : w ∈ LinearMap.range
      ((ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪).subtype.baseChange K) := by
    let incl : ↥Cor →ₗ[𝒪] ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪) :=
      (Cor.subtype.restrictScalars 𝒪).codRestrict _ (fun x => hpar x.1 x.2)
    have hincl : (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪).subtype ∘ₗ incl =
        Cor.subtype.restrictScalars 𝒪 := LinearMap.ext fun _ => rfl
    refine ⟨(incl ∘ₗ eM.toLinearMap).baseChange K v, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_assoc, hincl]

  obtain ⟨-, hC2, -⟩ :=
    CohCarrier.HeckeData.iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
      D Sp i₀ πk hπk K hinj
  have hRT : ∀ g : CohCarrier.Gen N (↑S : Set ℕ), ∃ R : Polynomial 𝒪, R.Monic ∧
      Polynomial.aeval (a (bg g)) R = 0 ∧
      R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar g)) ^ R.natDegree := by
    intro g
    by_contra hg
    have hbot := hC2 (fun g' => a (bg g')) ⟨g, hg⟩
    refine hw0 ((Submodule.mem_bot K).mp (hbot.le (Submodule.mem_inf.mpr
      ⟨(Submodule.mem_iInf _).mpr fun g' => ?_, hwrange⟩)))
    exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr (hwop g'))

  let a₀ : ℕ → K := fun q => if h : q.Prime ∧ q ∣ N then a (bg (CohCarrier.Gen.U q h.1 h.2)) else 0
  have ha₀ : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N), a₀ q = a (bg (CohCarrier.Gen.U q hq hqN)) :=
    fun q hq hqN => dif_pos ⟨hq, hqN⟩
  refine ⟨χ₀, a₀, fun q hq hqN => ⟨?_, ?_⟩⟩
  · rw [ha₀ q hq hqN]
    exact hRT (CohCarrier.Gen.U q hq hqN)
  · intro Mg _ hMgN g hg chig hchigT hchigU ι hι
    haveI : Module.Finite K (CohCarrier.H1 N ⊤ K) := CohCarrier.H1_moduleFinite N ⊤ K K
    have hu0 : Φ w ≠ 0 := fun h => hw0 (Φ.injective (h.trans (map_zero Φ).symm))
    obtain ⟨-, hB⟩ :=
      CohCarrier.finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
        N S hS hNS K Mg hMgN g hg chig hchigT hchigU ι a₀
    have hfin : ∀ (W : Submodule K (CohCarrier.H1 N ⊤ K)) (n : ℕ), Φ w ∈ W →
        Module.finrank K ↥W = 2 * n → n ≠ 0 := by
      intro W n huW hW
      have hp : 0 < Module.finrank K ↥W :=
        Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨Φ w, huW⟩, fun h => hu0 (congrArg Subtype.val h)⟩
      omega
    refine (Polynomial.rootMultiplicity_pos'.mp (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mp
      (hfin _ _ ?_ hB) q (Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩)))).2

    refine ⟨⟨?_, ?_⟩, ?_⟩
    ·
      rw [← hΦpar]
      exact Submodule.mem_map.mpr ⟨w, hwpar, rfl⟩
    ·
      refine (Submodule.mem_iInf _).mpr fun ℓ => (Submodule.mem_iInf _).mpr fun hℓ =>
        (Submodule.mem_iInf _).mpr fun hℓS => ?_
      have hℓN : ¬ ℓ ∣ N := fun h => hℓS (hNS ℓ hℓ h)
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      rw [Module.End.mem_eigenspace_iff]
      have h2 : (CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange K w = a (bg (CohCarrier.Gen.T ℓ hℓ hℓS hℓN)) • w :=
        hwop (CohCarrier.Gen.T ℓ hℓ hℓS hℓN)
      have h3 : a (bg (CohCarrier.Gen.T ℓ hℓ hℓS hℓN)) =
          χ₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) :=
        hvinj _ _ (by rw [← hvc, ← hF2 ℓ hℓ hℓS hℓN, hvT])
      show CohCarrier.heckeTL N ⊤ K ℓ (Φ w) = _ • Φ w
      rw [← hΦT ℓ w, h2, map_smul, h3]
      exact congrArg (fun x => x • Φ w) (hι ℓ hℓ hℓN hℓS).symm
    ·
      refine (Submodule.mem_iInf _).mpr fun q' => (Submodule.mem_iInf _).mpr fun hq' =>
        (Submodule.mem_iInf _).mpr fun hq'N => ?_
      haveI : NeZero q' := ⟨hq'.ne_zero⟩
      have h2 : (CohCarrier.heckeTL N ⊤ 𝒪 q').baseChange K w = a₀ q' • w := by
        rw [ha₀ q' hq' hq'N]; exact hwop (CohCarrier.Gen.U q' hq' hq'N)
      refine Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr ?_)
      show CohCarrier.heckeTL N ⊤ K q' (Φ w) = a₀ q' • Φ w
      rw [← hΦT q' w, h2, map_smul]

end S_CuspForm_heckeLocal_exists_algHom_algebraicClosure_residual_isRoot_of_linearEquiv_cornerSubmodule
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_algHom_algebraicClosure_residual_isRoot_of_linearEquiv_cornerSubmodule (solution)
