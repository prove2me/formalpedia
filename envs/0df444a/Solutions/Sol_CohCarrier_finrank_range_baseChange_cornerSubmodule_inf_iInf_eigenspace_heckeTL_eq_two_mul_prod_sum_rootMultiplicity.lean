-- Prove2me | solution 1 for CohCarrier.finrank_range_baseChange_cornerSubmodule_inf_iInf_eigenspace_heckeTL_eq_two_mul_prod_sum_rootMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/41b75601-24e2-5f22-972e-01b0ca636d3e

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Theorems.Thm_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
import Theorems.Thm_CohCarrier_exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms
import Theorems.Thm_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
import Theorems.Thm_CohCarrier_diamondL_top_apply
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_finrank_range_baseChange_cornerSubmodule_inf_iInf_eigenspace_heckeTL_eq_two_mul_prod_sum_rootMultiplicity
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex CuspForm.GammaH_finiteIndex WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one"
p2m_attr_erase "simp" "Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open Polynomial IsLocalRing Module
open scoped TensorProduct IsMulCommutative

namespace NewformCount

section IndepSum

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_eq_sum_of_iSupIndep {ι : Type} (p : ι → Submodule K V) (hind : iSupIndep p)
    (htop : iSup p = ⊤) (T : Finset ι) (hT : ∀ i, i ∉ T → p i = ⊥) :
    Module.finrank K V = ∑ i ∈ T, Module.finrank K ↥(p i) := by
  classical

  let p' : ↥T → Submodule K V := fun i => p i
  have hind' : iSupIndep p' := hind.comp Subtype.val_injective
  have htop' : iSup p' = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← htop]
    refine iSup_le fun i => ?_
    by_cases hi : i ∈ T
    · exact le_iSup p' ⟨i, hi⟩
    · rw [hT i hi]; exact bot_le
  have hint : DirectSum.IsInternal p' := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind' htop'
  let b := hint.collectedBasis fun i => Module.finBasis K ↥(p' i)
  rw [Module.finrank_eq_card_basis b, Fintype.card_sigma]
  rw [← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.card_fin]

end IndepSum

section DecompSum

theorem finrank_eq_sum_piFinset_finrank_iInf_maxGenEigenspace
    {F : Type} [Field F] [IsAlgClosed F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Module.End F V)
    (hc : ∀ i j, Commute (f i) (f j))
    (T : ι → Finset F)
    (hT : ∀ χ : ι → F, (∃ i, χ i ∉ T i) → (⨅ i, Module.End.maxGenEigenspace (f i) (χ i)) = ⊥) :
    Module.finrank F V =
      ∑ χ ∈ Fintype.piFinset T, Module.finrank F ↥(⨅ i, Module.End.maxGenEigenspace (f i) (χ i)) := by
  classical
  have hmaps : ∀ (i j : ι) (φ : F), Set.MapsTo ⇑(f i)
      ↑((f j).maxGenEigenspace φ) ↑((f j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo f hmaps
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  refine finrank_eq_sum_of_iSupIndep _ hind htop (Fintype.piFinset T) fun χ hχ => hT χ ?_
  by_contra h
  push Not at h
  exact hχ (Fintype.mem_piFinset.mpr h)

end DecompSum

section Transport

variable {K : Type} [CommRing K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]


theorem finrank_eq_sum_piFinset_finrank_iInf_maxGenEigenspace'
    {F : Type} [Field F] [IsAlgClosed F] {X : Type} [AddCommGroup X] [Module F X] (W : Submodule F X)
    [FiniteDimensional F W]
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Module.End F W)
    (hc : ∀ i j, Commute (f i) (f j))
    (T : ι → Finset F)
    (hT : ∀ χ : ι → F, (∃ i, χ i ∉ T i) → (⨅ i, Module.End.maxGenEigenspace (f i) (χ i)) = ⊥) :
    Module.finrank F W =
      ∑ χ ∈ Fintype.piFinset T, Module.finrank F ↥(⨅ i, Module.End.maxGenEigenspace (f i) (χ i)) :=
  finrank_eq_sum_piFinset_finrank_iInf_maxGenEigenspace f hc T hT
theorem map_eigenspace_of_comm (Φ : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ v, Φ (f v) = g (Φ v)) (μ : K) :
    Submodule.map (Φ : V →ₗ[K] W) (f.eigenspace μ) = g.eigenspace μ := by
  ext w
  simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [← h, hv, map_smul]
  · intro hw
    refine ⟨Φ.symm w, ?_, Φ.apply_symm_apply w⟩
    apply Φ.injective
    rw [h, Φ.apply_symm_apply, map_smul, Φ.apply_symm_apply, hw]

theorem comm_pow_sub (Φ : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ v, Φ (f v) = g (Φ v)) (μ : K) (k : ℕ) (v : V) :
    Φ (((f - μ • 1) ^ k) v) = ((g - μ • 1) ^ k) (Φ v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, h]

theorem map_maxGenEigenspace_of_comm (Φ : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ v, Φ (f v) = g (Φ v)) (μ : K) :
    Submodule.map (Φ : V →ₗ[K] W) (f.maxGenEigenspace μ) = g.maxGenEigenspace μ := by
  ext w
  simp only [Submodule.mem_map, Module.End.mem_maxGenEigenspace, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [← comm_pow_sub Φ f g h μ k v, hk, map_zero]⟩
  · rintro ⟨k, hk⟩
    refine ⟨Φ.symm w, ⟨k, ?_⟩, Φ.apply_symm_apply w⟩
    apply Φ.injective
    rw [comm_pow_sub Φ f g h μ k, Φ.apply_symm_apply, hk, map_zero]

end Transport

section Restrict

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem map_subtype_maxGenEigenspace_restrict (W : Submodule K V) (f : Module.End K V)
    (hf : ∀ v ∈ W, f v ∈ W) (μ : K) :
    Submodule.map W.subtype (Module.End.maxGenEigenspace (f.restrict hf) μ) = W ⊓ f.maxGenEigenspace μ := by
  show Submodule.map W.subtype ((Module.End.genEigenspace (f.restrict hf) μ) ⊤) = W ⊓ (f.genEigenspace μ) ⊤
  rw [Module.End.genEigenspace_restrict, Submodule.map_comap_subtype]

end Restrict

section Setting

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable abbrev opF (𝒪 : Type) [CommRing 𝒪] (F : Type) [Field F] [Algebra 𝒪 F]
    (S : Finset ℕ) (N : ℕ) [NeZero N] (g : CohCarrier.Gen N (↑S : Set ℕ)) :
    Module.End F (F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪) :=
  (CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g).baseChange F

noncomputable abbrev rangeC (F : Type) [Field F] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F] :
    Submodule F (F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪) :=
  LinearMap.range (((IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F)

theorem opF_comm {𝒪 : Type} [CommRing 𝒪] (F : Type) [Field F] [Algebra 𝒪 F]
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (g h : CohCarrier.Gen N (↑S : Set ℕ)) :
    opF 𝒪 F S N g * opF 𝒪 F S N h = opF 𝒪 F S N h * opF 𝒪 F S N g := by
  simp only [opF, ← LinearMap.baseChange_mul, hcomm g h]

theorem op_mem_corner {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (g : CohCarrier.Gen N (↑S : Set ℕ)) (x : CohCarrier.H1 N ⊤ 𝒪) (hx : x ∈ (IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))) :
    CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g x ∈ (IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) := by
  obtain ⟨y, rfl⟩ := hx
  let b : ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra :=
    ⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
      Algebra.subset_adjoin (Set.mem_range_self g)⟩
  refine ⟨b • y, ?_⟩
  show (Sp.e i₀) • (b • y) = CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g ((Sp.e i₀) • y)
  rw [smul_smul, mul_comm, ← smul_smul]
  rfl

theorem opF_mem_rangeC (F : Type) [Field F] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F]
    (g : CohCarrier.Gen N (↑S : Set ℕ)) (v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪)
    (hv : v ∈ rangeC F S N hcomm θbar Sp i₀) : opF 𝒪 F S N g v ∈ rangeC F S N hcomm θbar Sp i₀ := by
  obtain ⟨w, rfl⟩ := hv
  let CO : Submodule 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := (IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)).restrictScalars 𝒪
  have hg : ∀ x ∈ CO, CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g x ∈ CO :=
    fun x hx => op_mem_corner S N hcomm θbar Sp i₀ g x hx
  have hr : CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g ∘ₗ CO.subtype =
      CO.subtype ∘ₗ (CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g).restrict hg :=
    LinearMap.ext fun x => rfl
  refine ⟨((CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g).restrict hg).baseChange F w, ?_⟩
  have key : CO.subtype.baseChange F ∘ₗ ((CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g).restrict hg).baseChange F =
      (CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g).baseChange F ∘ₗ CO.subtype.baseChange F := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hr]
  exact LinearMap.congr_fun key w

theorem opF_mem_eigenspace {𝒪 : Type} [CommRing 𝒪] (F : Type) [Field F] [Algebra 𝒪 F]
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (g h : CohCarrier.Gen N (↑S : Set ℕ)) (μ : F) (v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪)
    (hv : v ∈ Module.End.eigenspace (opF 𝒪 F S N h) μ) : opF 𝒪 F S N g v ∈ Module.End.eigenspace (opF 𝒪 F S N h) μ := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [← Module.End.mul_apply, (opF_comm F S N hcomm g h).symm, Module.End.mul_apply, hv, map_smul]

theorem opF_mem_maxGenEigenspace {𝒪 : Type} [CommRing 𝒪] (F : Type) [Field F] [Algebra 𝒪 F]
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (g h : CohCarrier.Gen N (↑S : Set ℕ)) (μ : F) (v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪)
    (hv : v ∈ Module.End.maxGenEigenspace (opF 𝒪 F S N h) μ) :
    opF 𝒪 F S N g v ∈ Module.End.maxGenEigenspace (opF 𝒪 F S N h) μ :=
  Module.End.mapsTo_maxGenEigenspace_of_comm (opF_comm F S N hcomm h g) μ hv

end Setting

section FreeH1
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem free_H1' (N : ℕ) [NeZero N] : Module.Free 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := by
  haveI : Module.Finite 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := CohCarrier.H1_moduleFinite N ⊤ 𝒪 𝒪
  haveI : Module.IsTorsionFree 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := by
    refine ⟨fun r hr φ ψ h => ?_⟩
    ext x
    have := congrArg (fun (χ : CohCarrier.H1 N ⊤ 𝒪) => χ x) h
    simp only [AddMonoidHom.smul_apply, smul_eq_mul] at this
    exact hr.left this
  infer_instance
end FreeH1

section Systems

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem quad_ne_zero {F : Type} [Field F] (a b : F) : (X ^ 2 - C a * X + C b : Polynomial F) ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial F => p.coeff 2) h
  simp at this

theorem mem_primeFactors' {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) : q ∈ N.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩

noncomputable def sys {F : Type} (S : Finset ℕ) (N : ℕ) [NeZero N]
    (μT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N → F) (χ : ↥N.primeFactors → F) [One F] :
    CohCarrier.Gen N (↑S : Set ℕ) → F
  | .T ℓ hℓ hℓS hℓN => μT ℓ hℓ hℓS hℓN
  | .U q hq hqN => χ ⟨q, mem_primeFactors' hq hqN⟩
  | .dia _ => 1

theorem opF_dia (F : Type) [Field F] [Algebra 𝒪 F] (S : Finset ℕ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) :
    opF 𝒪 F S N (CohCarrier.Gen.dia d) = 1 := by
  have h1 : CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 (CohCarrier.Gen.dia d) = LinearMap.id :=
    LinearMap.ext fun φ => CohCarrier.diamondL_top_apply N 𝒪 d φ
  show (CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 (CohCarrier.Gen.dia d)).baseChange F = 1
  rw [h1, LinearMap.baseChange_id]
  rfl

theorem maxGenEigenspace_one_one {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] :
    Module.End.maxGenEigenspace (1 : Module.End F V) 1 = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp⟩

theorem residualTest_one {F : Type} [Field F] [Algebra 𝒪 F] :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (1 : F) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (1 : ResidueField 𝒪)) ^ R.natDegree) := by
  refine ⟨Polynomial.X - Polynomial.C 1, Polynomial.monic_X_sub_C 1, by simp, ?_⟩
  rw [Polynomial.natDegree_X_sub_C, pow_one, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_one]

theorem θbar_dia (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N (↑S : Set ℕ), πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (d : (ZMod N)ˣ) : θbar (CohCarrier.Gen.dia d) = 1 := by
  rw [← hπk]
  have h1 : (⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.dia d),
      Algebra.subset_adjoin (Set.mem_range_self (CohCarrier.Gen.dia d))⟩ :
        ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra) = 1 := by
    apply Subtype.ext
    show CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 (CohCarrier.Gen.dia d) = 1
    exact LinearMap.ext fun φ => CohCarrier.diamondL_top_apply N 𝒪 d φ
  rw [h1, map_one, map_one]

end Systems

section Pieces

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

noncomputable abbrev Wsp (F : Type) [Field F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F] (μT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N → F) :
    Submodule F (F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪) :=
  rangeC F S N hcomm θbar Sp i₀ ⊓
    ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      Module.End.eigenspace (opF 𝒪 F S N (CohCarrier.Gen.T ℓ hℓ hℓS hℓN)) (μT ℓ hℓ hℓS hℓN)

noncomputable abbrev piece (F : Type) [Field F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F] (μT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N → F)
    (χ : ↥N.primeFactors → F) : Submodule F (F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪) :=
  Wsp F S N hcomm θbar Sp i₀ μT ⊓
    ⨅ q : ↥N.primeFactors, Module.End.maxGenEigenspace
      (opF 𝒪 F S N (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2))) (χ q)

noncomputable abbrev Vsys (F : Type) [Field F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F]
    (a : CohCarrier.Gen N (↑S : Set ℕ) → F) : Submodule F (F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪) :=
  ⨅ g : (CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).Gen, Module.End.maxGenEigenspace (((CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g).baseChange F) (a g)

theorem piece_le_Vsys (F : Type) [Field F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F] (μT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N → F)
    (χ : ↥N.primeFactors → F) :
    piece F S N hcomm θbar Sp i₀ μT χ ≤ Vsys F S N hcomm θbar Sp i₀ (sys S N μT χ) := by
  intro v hv
  have hW : v ∈ Wsp F S N hcomm θbar Sp i₀ μT := (Submodule.mem_inf.mp hv).1
  have hU := Submodule.mem_iInf _ |>.mp (Submodule.mem_inf.mp hv).2
  have hT := Submodule.mem_iInf _ |>.mp (Submodule.mem_inf.mp hW).2
  refine (Submodule.mem_iInf _).mpr fun g => ?_
  cases g with
  | T ℓ hℓ hℓS hℓN =>
    have h := ((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp (hT ℓ)) hℓ)) hℓS)) hℓN
    exact Module.End.eigenspace_le_maxGenEigenspace h
  | U q hq hqN =>
    exact hU ⟨q, mem_primeFactors' hq hqN⟩
  | dia d =>
    show v ∈ Module.End.maxGenEigenspace (opF 𝒪 F S N (CohCarrier.Gen.dia d)) 1
    rw [opF_dia, maxGenEigenspace_one_one]
    exact Submodule.mem_top

theorem piece_eq_bot_of_not_pass (F : Type) [Field F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F]
    (hinj : Function.Injective (algebraMap 𝒪 F))
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N (↑S : Set ℕ), πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (μT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N → F) (χ : ↥N.primeFactors → F) (q : ↥N.primeFactors)
    (hq : ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (χ q) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2)))) ^ R.natDegree)) :
    piece F S N hcomm θbar Sp i₀ μT χ = ⊥ := by
  haveI : Module.Finite 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := CohCarrier.H1_moduleFinite N ⊤ 𝒪 𝒪
  haveI : Module.Free 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := free_H1' N
  have hCD := CohCarrier.HeckeData.iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
    (CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar) Sp i₀ πk hπk F hinj
  obtain ⟨-, hCD2, -⟩ := hCD
  have hbot := hCD2 (sys S N μT χ)
    ⟨CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2), hq⟩
  rw [eq_bot_iff, ← hbot]
  refine le_inf (piece_le_Vsys F S N hcomm θbar Sp i₀ μT χ) ?_
  exact inf_le_left.trans inf_le_left

end Pieces

section TransportH1

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem rangeC_le_rangePar (F : Type) [Field F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F] (hpar : ∀ v : CohCarrier.H1 N ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) → v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪)) :
    rangeC F S N hcomm θbar Sp i₀ ≤ LinearMap.range ((ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪).subtype.baseChange F) := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    refine ⟨a ⊗ₜ[𝒪] ⟨(c : CohCarrier.H1 N ⊤ 𝒪), hpar _ c.2⟩, ?_⟩
    simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype, LinearMap.coe_restrictScalars]
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

theorem opF_T (F : Type) [Field F] [Algebra 𝒪 F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) :
    opF 𝒪 F S N (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange F := rfl

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem opF_U (F : Type) [Field F] [Algebra 𝒪 F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) :
    opF 𝒪 F S N (CohCarrier.Gen.U q hq hqN) =
      (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 q).baseChange F := rfl

theorem map_piece_eq (F : Type) [Field F] (S : Finset ℕ) (N : ℕ) [NeZero N]
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F]
    (hinj : Function.Injective (algebraMap 𝒪 F)) (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N (↑S : Set ℕ), πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hpar : ∀ v : CohCarrier.H1 N ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) → v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪))
    (μT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N → F) (hresT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (μT ℓ hℓ hℓS hℓN) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN))) ^ R.natDegree))
    (χ : ↥N.primeFactors → F)
    (hpass : ∀ q : ↥N.primeFactors,
      (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (χ q) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2)))) ^ R.natDegree))
    (Φ : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪 ≃ₗ[F] CohCarrier.H1 N ⊤ F)
    (hΦT : ∀ (ℓ : ℕ) [NeZero ℓ] (v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪),
      Φ ((CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange F v) = CohCarrier.heckeTL N ⊤ F ℓ (Φ v))
    (hΦpar : Submodule.map (Φ : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪 →ₗ[F] CohCarrier.H1 N ⊤ F)
        (LinearMap.range ((ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪).subtype.baseChange F)) = (ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F)) :
    Submodule.map (Φ : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪 →ₗ[F] CohCarrier.H1 N ⊤ F) (piece F S N hcomm θbar Sp i₀ μT χ) =
    (ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F) ⊓
      (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
        Module.End.eigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ) (μT ℓ hℓ hℓS hℓN)) ⊓
      (⨅ q : ↥N.primeFactors, Module.End.maxGenEigenspace
        (haveI : NeZero (q : ℕ) := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩; CohCarrier.heckeTL N ⊤ F q)
        (χ q)) := by
  classical
  haveI : Module.Finite 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := CohCarrier.H1_moduleFinite N ⊤ 𝒪 𝒪
  haveI : Module.Free 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := free_H1' N
  have hCD := CohCarrier.HeckeData.iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
    (CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar) Sp i₀ πk hπk F hinj
  obtain ⟨hCD1, -, -⟩ := hCD

  have hsys : ∀ g : CohCarrier.Gen N (↑S : Set ℕ),
      (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (sys S N μT χ g) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar g)) ^ R.natDegree) := by
    intro g
    cases g with
    | T ℓ hℓ hℓS hℓN => exact hresT ℓ hℓ hℓS hℓN
    | U q hq hqN => exact hpass ⟨q, mem_primeFactors' hq hqN⟩
    | dia d =>
      show (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (1 : F) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.dia d))) ^ R.natDegree)
      rw [θbar_dia S N hcomm θbar Sp i₀ πk hπk d]
      exact residualTest_one
  have hVle : Vsys F S N hcomm θbar Sp i₀ (sys S N μT χ) ≤ rangeC F S N hcomm θbar Sp i₀ := hCD1 _ hsys

  have hTmem : ∀ (ℓ : ℕ) [NeZero ℓ] (μ : F) (v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪),
      v ∈ Module.End.eigenspace ((CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange F) μ ↔
        Φ v ∈ Module.End.eigenspace (CohCarrier.heckeTL N ⊤ F ℓ) μ := by
    intro ℓ _ μ v
    rw [← map_eigenspace_of_comm Φ _ _ (hΦT ℓ) μ, Submodule.mem_map]
    constructor
    · exact fun h => ⟨v, h, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      have hwv' : w = v := Φ.injective (by simpa using hwv)
      subst hwv'
      exact hw
  have hUmem : ∀ (q : ℕ) [NeZero q] (μ : F) (v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪),
      v ∈ Module.End.maxGenEigenspace ((CohCarrier.heckeTL N ⊤ 𝒪 q).baseChange F) μ ↔
        Φ v ∈ Module.End.maxGenEigenspace (CohCarrier.heckeTL N ⊤ F q) μ := by
    intro q _ μ v
    rw [← map_maxGenEigenspace_of_comm Φ _ _ (hΦT q) μ, Submodule.mem_map]
    constructor
    · exact fun h => ⟨v, h, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      have hwv' : w = v := Φ.injective (by simpa using hwv)
      subst hwv'
      exact hw

  have hParmem : ∀ v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪,
      v ∈ LinearMap.range ((ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪).subtype.baseChange F) ↔ Φ v ∈ (ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F) := by
    intro v
    rw [← hΦpar, Submodule.mem_map]
    constructor
    · exact fun h => ⟨v, h, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      have hwv' : w = v := Φ.injective (by simpa using hwv)
      subst hwv'
      exact hw
  apply le_antisymm
  ·
    rintro x ⟨v, hv, rfl⟩
    have hW : v ∈ Wsp F S N hcomm θbar Sp i₀ μT := (Submodule.mem_inf.mp hv).1
    have hU := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hv).2
    have hR : v ∈ rangeC F S N hcomm θbar Sp i₀ := (Submodule.mem_inf.mp hW).1
    have hT := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hW).2
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (hParmem v).mp (rangeC_le_rangePar F S N hcomm θbar Sp i₀ hpar hR)
    · refine (Submodule.mem_iInf _).mpr fun ℓ => (Submodule.mem_iInf _).mpr fun hℓ =>
        (Submodule.mem_iInf _).mpr fun hℓS => (Submodule.mem_iInf _).mpr fun hℓN => ?_
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have h := ((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp (hT ℓ)) hℓ)) hℓS)) hℓN
      exact (hTmem ℓ _ v).mp h
    · refine (Submodule.mem_iInf _).mpr fun q => ?_
      haveI : NeZero (q : ℕ) := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
      exact (hUmem q _ v).mp (hU q)
  ·
    intro x hx
    obtain ⟨⟨hxP, hxT⟩, hxU⟩ := Submodule.mem_inf.mp hx |>.imp (Submodule.mem_inf.mp) id
    set v := Φ.symm x with hv
    have hxv : Φ v = x := Φ.apply_symm_apply x
    have hT' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
        v ∈ Module.End.eigenspace (opF 𝒪 F S N (CohCarrier.Gen.T ℓ hℓ hℓS hℓN)) (μT ℓ hℓ hℓS hℓN) := by
      intro ℓ hℓ hℓS hℓN
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have h := ((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp
        (((Submodule.mem_iInf _).mp hxT) ℓ)) hℓ)) hℓS)) hℓN
      rw [opF_T]
      exact (hTmem ℓ _ v).mpr (hxv ▸ h)
    have hU' : ∀ q : ↥N.primeFactors, v ∈ Module.End.maxGenEigenspace
        (opF 𝒪 F S N (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2))) (χ q) := by
      intro q
      haveI : NeZero (q : ℕ) := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
      have h := ((Submodule.mem_iInf _).mp hxU) q
      rw [opF_U]
      exact (hUmem q _ v).mpr (hxv ▸ h)

    have hvV : v ∈ Vsys F S N hcomm θbar Sp i₀ (sys S N μT χ) := by
      refine (Submodule.mem_iInf _).mpr fun g => ?_
      cases g with
      | T ℓ hℓ hℓS hℓN => exact Module.End.eigenspace_le_maxGenEigenspace (hT' ℓ hℓ hℓS hℓN)
      | U q hq hqN => exact hU' ⟨q, mem_primeFactors' hq hqN⟩
      | dia d =>
        show v ∈ Module.End.maxGenEigenspace (opF 𝒪 F S N (CohCarrier.Gen.dia d)) 1
        rw [opF_dia, maxGenEigenspace_one_one]
        exact Submodule.mem_top
    have hvR : v ∈ rangeC F S N hcomm θbar Sp i₀ := hVle hvV
    refine ⟨v, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hvR, ?_⟩, ?_⟩, hxv⟩
    · exact (Submodule.mem_iInf _).mpr fun ℓ => (Submodule.mem_iInf _).mpr fun hℓ =>
        (Submodule.mem_iInf _).mpr fun hℓS => (Submodule.mem_iInf _).mpr fun hℓN => hT' ℓ hℓ hℓS hℓN
    · exact (Submodule.mem_iInf _).mpr fun q => hU' q

end TransportH1

section Count

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem mem_maxGenEigenspace_restrict_iff {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (W : Submodule K V) (f : Module.End K V) (hf : ∀ v ∈ W, f v ∈ W) (μ : K) (w : ↥W) :
    w ∈ Module.End.maxGenEigenspace (f.restrict hf) μ ↔ (w : V) ∈ f.maxGenEigenspace μ := by
  show w ∈ (Module.End.genEigenspace (f.restrict hf) μ) ⊤ ↔ (w : V) ∈ (f.genEigenspace μ) ⊤
  rw [Module.End.genEigenspace_restrict, Submodule.mem_comap, Submodule.coe_subtype]

open scoped Classical in

theorem count_general (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hcomm : ∀ g h : CohCarrier.Gen N (↑S : Set ℕ),
      CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily N ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen N (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N (↑S : Set ℕ), πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hpar : ∀ v : CohCarrier.H1 N ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) → v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪))
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
    (hchigT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
    (hchigU : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg),
      chig (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = ModularFormClass.qCoeff g q)
    (ι : chig.range →+* F)
    (hres : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN))
              (Set.notMem_empty ℓ)))) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN))) ^ R.natDegree)) :
    Module.finrank F
        ↥(LinearMap.range (((IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) ⊓
          ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N), Module.End.eigenspace
            ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange F)
            (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN))
              (Set.notMem_empty ℓ))))) =
      2 * ∏ q ∈ N.primeFactors, (if h : q.Prime ∧ q ∣ N then
        (let P : Polynomial (F) :=
          (if hqP : Nat.Prime q then
            (let aq : F := if hqMg : q ∣ Mg
                then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hqP hqMg (Set.notMem_empty q)))
                else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hqP hqMg (Set.notMem_empty q)))
             let e : ℕ := N.factorization q - Mg.factorization q
             if e = 0 then X - C aq
             else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : F) else (q : F))))
           else 1)
         ∑ x ∈ P.roots.toFinset,
          if (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q h.1 h.2))) ^ R.natDegree)
          then P.rootMultiplicity x else 0)
        else 1) := by
  haveI : Module.Finite 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := CohCarrier.H1_moduleFinite N ⊤ 𝒪 𝒪
  haveI : Module.Free 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := free_H1' N

  let μT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N → F := fun ℓ hℓ hℓS hℓN =>
    ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN)) (Set.notMem_empty ℓ)))
  let P : ℕ → Polynomial F := fun q => (if hqP : Nat.Prime q then
      (let aq : F := if hqMg : q ∣ Mg
          then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hqP hqMg (Set.notMem_empty q)))
          else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hqP hqMg (Set.notMem_empty q)))
       let e : ℕ := N.factorization q - Mg.factorization q
       if e = 0 then X - C aq
       else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : F) else (q : F))))
     else 1)

  have hW : (LinearMap.range (((IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) ⊓
          ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N), Module.End.eigenspace
            ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange F)
            (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN))
              (Set.notMem_empty ℓ))))) = Wsp F S N hcomm θbar Sp i₀ μT := rfl
  rw [hW]

  have hBC := CohCarrier.exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms F hinj N ⊤
  obtain ⟨Φ, -, hΦT, hΦpar⟩ := hBC
  have hES := fun lam : ℕ → F =>
    (CohCarrier.finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
      N S hS hNS F Mg hMgN g hg chig hchigT hchigU ι lam).2

  have hN : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N := fun ℓ hℓ hℓS h => hℓS (hNS ℓ hℓ h)

  have hWU : ∀ (q : ↥N.primeFactors) (v : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪), v ∈ Wsp F S N hcomm θbar Sp i₀ μT →
      opF 𝒪 F S N (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2)) v ∈
        Wsp F S N hcomm θbar Sp i₀ μT := by
    intro q v hv
    refine Submodule.mem_inf.mpr ⟨opF_mem_rangeC F S N hcomm θbar Sp i₀ _ v (Submodule.mem_inf.mp hv).1, ?_⟩
    have hT := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hv).2
    refine (Submodule.mem_iInf _).mpr fun ℓ => (Submodule.mem_iInf _).mpr fun hℓ =>
      (Submodule.mem_iInf _).mpr fun hℓS => (Submodule.mem_iInf _).mpr fun hℓN => ?_
    exact opF_mem_eigenspace F S N hcomm _ _ _ v
      (((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp (((Submodule.mem_iInf _).mp (hT ℓ)) hℓ)) hℓS)) hℓN)

  let f : ↥N.primeFactors → Module.End F ↥(Wsp F S N hcomm θbar Sp i₀ μT) := fun q =>
    (opF 𝒪 F S N (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2))).restrict (hWU q)
  have hfc : ∀ i j, Commute (f i) (f j) := by
    intro i j
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    show (opF 𝒪 F S N _ * opF 𝒪 F S N _) (w : F ⊗[𝒪] CohCarrier.H1 N ⊤ 𝒪) = (opF 𝒪 F S N _ * opF 𝒪 F S N _) w
    rw [opF_comm F S N hcomm]

  have hmap : ∀ χ : ↥N.primeFactors → F,
        Submodule.map (Wsp F S N hcomm θbar Sp i₀ μT).subtype (⨅ q, Module.End.maxGenEigenspace (M := ↥(Wsp F S N hcomm θbar Sp i₀ μT)) (f q) (χ q)) =
        piece F S N hcomm θbar Sp i₀ μT χ := by
    intro χ
    ext v
    simp only [Submodule.mem_map, Submodule.mem_iInf, Submodule.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Submodule.mem_inf.mpr ⟨w.2, (Submodule.mem_iInf _).mpr fun q =>
        (mem_maxGenEigenspace_restrict_iff _ _ (hWU q) (χ q) w).mp (hw q)⟩
    · intro hv
      refine ⟨⟨v, (Submodule.mem_inf.mp hv).1⟩, fun q => ?_, rfl⟩
      exact (mem_maxGenEigenspace_restrict_iff _ _ (hWU q) (χ q) _).mpr (((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hv).2) q)
  have hfr : ∀ χ : ↥N.primeFactors → F,
      Module.finrank F ↥(⨅ q, Module.End.maxGenEigenspace (M := ↥(Wsp F S N hcomm θbar Sp i₀ μT)) (f q) (χ q)) = Module.finrank F ↥(piece F S N hcomm θbar Sp i₀ μT χ) := by
    intro χ; rw [← hmap χ, Submodule.finrank_map_subtype_eq]

  have hdim : ∀ χ : ↥N.primeFactors → F,
      (∀ q : ↥N.primeFactors, (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (χ q) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2)))) ^ R.natDegree)) →
      Module.finrank F ↥(piece F S N hcomm θbar Sp i₀ μT χ) = 2 * ∏ q : ↥N.primeFactors, (P q).rootMultiplicity (χ q) := by
    intro χ hpass

    let lam : ℕ → F := fun q => if h : q ∈ N.primeFactors then χ ⟨q, h⟩ else 0
    have hlam : ∀ q : ↥N.primeFactors, lam q = χ q := fun q => by
      show (if h : (q : ℕ) ∈ N.primeFactors then χ ⟨q, h⟩ else 0) = χ q
      rw [dif_pos q.2]
    rw [← LinearEquiv.finrank_map_eq Φ, map_piece_eq F S N hcomm θbar Sp i₀ hinj πk hπk hpar μT hres χ hpass Φ hΦT hΦpar]

    have key := hES lam
    have hbridge :
        (ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F ⊓
          (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
            Module.End.eigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ) (μT ℓ hℓ hℓS hℓN)) ⊓
          (⨅ q : ↥N.primeFactors, Module.End.maxGenEigenspace
            (haveI : NeZero (q : ℕ) := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩; CohCarrier.heckeTL N ⊤ F q) (χ q))) =
        (ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F ⊓
          (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S), Module.End.eigenspace
            (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ)
            (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
              (fun h => hℓS (hNS ℓ hℓ (h.trans hMgN))) (Set.notMem_empty ℓ))))) ⊓
          (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), Module.End.maxGenEigenspace
            (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ F q) (lam q))) := by
      refine congrArg₂ (· ⊓ ·) (congrArg₂ (· ⊓ ·) rfl ?_) ?_
      · refine iInf_congr fun ℓ => iInf_congr fun hℓ => iInf_congr fun hℓS => ?_
        exact iInf_pos (hN ℓ hℓ hℓS)
      · apply le_antisymm
        · refine le_iInf fun q => le_iInf fun hq => le_iInf fun hqN => ?_
          have h := iInf_le (fun q : ↥N.primeFactors => Module.End.maxGenEigenspace
            (haveI : NeZero (q : ℕ) := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩; CohCarrier.heckeTL N ⊤ F q) (χ q))
            ⟨q, mem_primeFactors' hq hqN⟩
          rw [← hlam ⟨q, mem_primeFactors' hq hqN⟩] at h
          exact h
        · refine le_iInf fun q => ?_
          intro v hv
          have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hv (q : ℕ))
            (Nat.prime_of_mem_primeFactors q.2)) (Nat.dvd_of_mem_primeFactors q.2)
          rw [hlam q] at h
          exact h
    rw [hbridge, key, ← Finset.prod_coe_sort N.primeFactors]
    refine congrArg _ ?_
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hlam q]

  let T : ↥N.primeFactors → Finset F := fun q =>
    ((P q).roots.toFinset).filter fun x =>
      (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2)))) ^ R.natDegree)
  have hP0 : ∀ q : ↥N.primeFactors, P q ≠ 0 := by
    intro q
    show (if hqP : Nat.Prime (q : ℕ) then
        (let aq : F := if hqMg : (q : ℕ) ∣ Mg
            then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hqP hqMg (Set.notMem_empty (q : ℕ))))
            else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hqP hqMg (Set.notMem_empty (q : ℕ))))
         let e : ℕ := N.factorization (q : ℕ) - Mg.factorization (q : ℕ)
         if e = 0 then X - C aq
         else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if (q : ℕ) ∣ Mg then (0 : F) else ((q : ℕ) : F))))
       else 1) ≠ 0
    rw [dif_pos (Nat.prime_of_mem_primeFactors q.2)]
    dsimp only
    split_ifs <;> first
      | exact Polynomial.X_sub_C_ne_zero _
      | exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (quad_ne_zero _ _)
  have hbot : ∀ χ : ↥N.primeFactors → F, (∃ q, χ q ∉ T q) →
      (⨅ q, Module.End.maxGenEigenspace (M := ↥(Wsp F S N hcomm θbar Sp i₀ μT)) (f q) (χ q)) = ⊥ := by
    rintro χ ⟨q, hq⟩
    refine (Submodule.finrank_eq_zero
      (S := ⨅ q, Module.End.maxGenEigenspace (M := ↥(Wsp F S N hcomm θbar Sp i₀ μT)) (f q) (χ q))).mp ?_
    rw [hfr χ]
    rw [Finset.mem_filter, not_and_or] at hq
    by_cases hpass : ∀ q : ↥N.primeFactors,
        (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (χ q) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q.1 (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2)))) ^ R.natDegree)
    ·
      rcases hq with hq | hq
      · rw [hdim χ hpass, Finset.prod_eq_zero (Finset.mem_univ q), mul_zero]
        apply Polynomial.rootMultiplicity_eq_zero
        intro hroot
        exact hq (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hP0 q)).mpr hroot))
      · exact absurd (hpass q) hq
    · obtain ⟨q', hq'⟩ := not_forall.mp hpass
      rw [piece_eq_bot_of_not_pass F S N hcomm θbar Sp i₀ hinj πk hπk μT χ q' hq', finrank_bot]

  have hsum := finrank_eq_sum_piFinset_finrank_iInf_maxGenEigenspace' (Wsp F S N hcomm θbar Sp i₀ μT) f hfc T hbot

  rw [hsum]
  have hterm : ∀ χ ∈ Fintype.piFinset T,
      Module.finrank F ↥(⨅ q, Module.End.maxGenEigenspace (M := ↥(Wsp F S N hcomm θbar Sp i₀ μT)) (f q) (χ q)) = 2 * ∏ q : ↥N.primeFactors, (P q).rootMultiplicity (χ q) := by
    intro χ hχ
    rw [hfr χ]
    refine hdim χ fun q => ?_
    exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hχ q)).2
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    show (∑ χ ∈ Fintype.piFinset T, ∏ q : ↥N.primeFactors, (P q).rootMultiplicity (χ q)) =
        ∏ q : ↥N.primeFactors, ∑ y ∈ T q, (P q).rootMultiplicity y from
      (Finset.prod_univ_sum T (fun (q : ↥N.primeFactors) (y : F) => (P q).rootMultiplicity y)).symm,
    ← Finset.prod_coe_sort N.primeFactors]
  refine congrArg _ ?_
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [dif_pos (And.intro (Nat.prime_of_mem_primeFactors q.2) (Nat.dvd_of_mem_primeFactors q.2))]
  show ∑ x ∈ T q, (P q).rootMultiplicity x = _
  rw [Finset.sum_filter]

end Count

end NewformCount

namespace NewformCount

theorem algebraMap_algebraicClosure_injective {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] :
    Function.Injective (algebraMap 𝒪 (AlgebraicClosure (FractionRing 𝒪))) := by
  rw [IsScalarTower.algebraMap_eq 𝒪 (FractionRing 𝒪) (AlgebraicClosure (FractionRing 𝒪)),
    RingHom.coe_comp]
  exact (algebraMap (FractionRing 𝒪) _).injective.comp (IsFractionRing.injective 𝒪 (FractionRing 𝒪))

end NewformCount

open NewformCount in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open scoped Classical in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)

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

    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
    (hchigT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
    (hchigU : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg),
      chig (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = ModularFormClass.qCoeff g q)
    (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪))
    (hres : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN))
              (Set.notMem_empty ℓ)))) R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN))) ^ R.natDegree)) :
    Module.finrank (AlgebraicClosure (FractionRing 𝒪))
        ↥(LinearMap.range (((IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange (AlgebraicClosure (FractionRing 𝒪))) ⊓
          ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N), Module.End.eigenspace
            ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ).baseChange (AlgebraicClosure (FractionRing 𝒪)))
            (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN))
              (Set.notMem_empty ℓ))))) =
      2 * ∏ q ∈ N.primeFactors, (if h : q.Prime ∧ q ∣ N then
        (let P : Polynomial (AlgebraicClosure (FractionRing 𝒪)) :=
          (if hqP : Nat.Prime q then
            (let aq : AlgebraicClosure (FractionRing 𝒪) := if hqMg : q ∣ Mg
                then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hqP hqMg (Set.notMem_empty q)))
                else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hqP hqMg (Set.notMem_empty q)))
             let e : ℕ := N.factorization q - Mg.factorization q
             if e = 0 then X - C aq
             else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : AlgebraicClosure (FractionRing 𝒪)) else (q : AlgebraicClosure (FractionRing 𝒪)))))
           else 1)
         ∑ x ∈ P.roots.toFinset,
          if (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (θbar (CohCarrier.Gen.U q h.1 h.2))) ^ R.natDegree)
          then P.rootMultiplicity x else 0)
        else 1) :=
  count_general (AlgebraicClosure (FractionRing 𝒪)) S hS N hNS hcomm θbar Sp i₀
    algebraMap_algebraicClosure_injective πk hπk hpar Mg hMgN g hg chig hchigT hchigU ι hres

end S_CohCarrier_finrank_range_baseChange_cornerSubmodule_inf_iInf_eigenspace_heckeTL_eq_two_mul_prod_sum_rootMultiplicity
end P2MW
export P2MW.S_CohCarrier_finrank_range_baseChange_cornerSubmodule_inf_iInf_eigenspace_heckeTL_eq_two_mul_prod_sum_rootMultiplicity (solution)
