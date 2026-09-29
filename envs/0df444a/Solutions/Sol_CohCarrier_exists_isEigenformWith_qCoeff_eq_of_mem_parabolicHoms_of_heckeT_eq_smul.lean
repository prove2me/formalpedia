-- Prove2me | solution 1 for CohCarrier.exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/625fa851-0134-52d1-bbc0-6b304c6c1bed

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularCurve_existsUnique_periodMapOf_add_conj_periodMapOf_eq_of_mem_parabolicHoms
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import Theorems.Thm_CohCarrier_heckeT_apply_eq_sumEquiv
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
import Theorems.Thm_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"
p2m_attr_erase "simp" "CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

noncomputable section

open ModularCurve ModularCurve.Period CohCarrier CongruenceSubgroup ModularFormClass UpperHalfPlane Filter Topology

open scoped MatrixGroups ComplexConjugate ModularForm

namespace EsUPar

namespace PerU

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a) (-(1 : ℂ) * a) t := by
    simpa using ((hasDerivAt_const t (1 : ℂ)).sub h1).mul_const a
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * b) (1 * b) t := h1.mul_const b
  have := h2.add h3
  convert this using 1 <;> first | rfl | ring

theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * (τ₀ : ℂ) + (t : ℂ) * (τ₁ : ℂ) := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem periodAlongOf_eq_sub (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2)
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ := by
  rw [ModularCurve.periodAlongOf_apply]
  set g : ℝ → ℂ := fun t => F (ModularCurve.segmentPath τ₀ τ₁ t) with hg
  have hgF : ∀ t, g t = (F ∘ ofComplex) (ModularCurve.segmentPoint τ₀ τ₁ t) := by
    intro t
    simp only [hg, Function.comp]
    congr 1
    rw [← ModularCurve.coe_segmentPath, ofComplex_apply]
  have hg0 : g 0 = F τ₀ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 0 = (τ₀ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨le_rfl, zero_le_one⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hg1 : g 1 = F τ₁ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 1 = (τ₁ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨zero_le_one, le_rfl⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hFcont : ∀ τ : ℍ, ContinuousAt (F ∘ ofComplex) (τ : ℂ) := fun τ => (hF τ).continuousAt
  have hgcont : Continuous g := by
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    refine continuous_iff_continuousAt.mpr fun t => ?_
    refine ContinuousAt.comp ?_ (ModularCurve.continuous_segmentPoint τ₀ τ₁).continuousAt
    have := hFcont (ModularCurve.segmentPath τ₀ τ₁ t)
    rwa [ModularCurve.coe_segmentPath] at this
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hpath : HasDerivAt (ModularCurve.segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t := by
      refine (hasDerivAt_affine (τ₀ : ℂ) (τ₁ : ℂ) t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact segmentPoint_eq_of_mem (Set.Ioo_subset_Icc_self hs)
    have hFat : HasDerivAt (F ∘ ofComplex) (f (ModularCurve.segmentPath τ₀ τ₁ t))
        (ModularCurve.segmentPoint τ₀ τ₁ t) := by
      have := hF (ModularCurve.segmentPath τ₀ τ₁ t)
      rwa [ModularCurve.coe_segmentPath] at this
    have hcomp := hFat.comp t hpath
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    exact hcomp
  have hint : IntervalIntegrable
      (fun t => f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) MeasureTheory.volume 0 1 :=
    ModularCurve.intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hgcont.continuousOn hderiv hint
  rw [key, hg0, hg1]

theorem hasDerivAt_comp_smul {F : ℍ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) {β : GL (Fin 2) ℝ}
    (hβ : 0 < ((β : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => F (β • ofComplex z)) ((f ∣[(2 : ℤ)] β) τ) ↑τ := by
  have hfun : (fun z : ℂ => F (β • ofComplex z))
      = (F ∘ ofComplex) ∘ (fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (F ∘ ofComplex) (f (β • τ))
      ((fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hF (β • τ)
  have hcomp := houter.comp (↑τ : ℂ) (UpperHalfPlane.hasStrictDerivAt_smul hβ τ).hasDerivAt
  rw [← hfun] at hcomp
  convert hcomp using 1 <;> try rfl
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos (by exact_mod_cast hβ)]
  simp only [ContinuousAlgEquiv.refl_apply, Matrix.GeneralLinearGroup.val_det_apply]
  rw [abs_of_pos (by exact_mod_cast hβ), show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, zpow_neg,
    div_eq_mul_inv, zpow_two, pow_two]
  ring

section Alpha

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

abbrev alpha : GL (Fin 2) ℝ := ModularForm.heckeMatrix ℓ 0

theorem mapGL_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ i j : ℤ) : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL]

variable [NeZero ℓ]

theorem alpha_mul_mapGL (γ : ↥(GammaHUpper M H ℓ)) :
    alpha ℓ * Matrix.SpecialLinearGroup.mapGL ℝ ((γ : ↥(GammaH M H)) : SL(2, ℤ)) =
      Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ γ : ↥(GammaH M H)) : SL(2, ℤ)) * alpha ℓ := by
  have hℓ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  obtain ⟨m, hm⟩ := dvd_of_mem_GammaHUpper M H ℓ γ
  have hc : ∀ i j, (((conjL M H ℓ γ : ↥(GammaH M H)) : SL(2, ℤ)) i j : ℤ) =
      (conjUpperMat ℓ ((γ : ↥(GammaH M H)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M H ℓ γ)) i j :=
    fun _ _ => rfl
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, mapGL_apply, mapGL_apply, mapGL_apply, mapGL_apply, hc, hc]
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, ModularForm.val_heckeMatrix (NeZero.ne ℓ), hm, Int.mul_ediv_cancel_left _ hℓ] <;> ring

end Alpha

section Transversal

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) {ι : Type*}
  (e : ι ≃ Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)))

abbrev r (i : ι) : ↥(GammaH M H) := rep (GammaHUpper M H ℓ) (e i)

def beta (i : ι) : GL (Fin 2) ℝ :=
  alpha ℓ * Matrix.SpecialLinearGroup.mapGL ℝ ((r M H ℓ e i : ↥(GammaH M H)) : SL(2, ℤ))

theorem det_beta_pos (i : ι) : 0 < ((beta M H ℓ e i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [beta, Units.val_mul, Matrix.det_mul, ← Matrix.GeneralLinearGroup.val_det_apply,
    ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one,
    mul_one]
  exact ModularForm.det_heckeMatrix_pos ℓ 0

def perm (γ : ↥(GammaH M H)) (i : ι) : ι :=
  e.symm (cls (GammaHUpper M H ℓ) (r M H ℓ e i * γ))

theorem e_perm (γ : ↥(GammaH M H)) (i : ι) :
    e (perm M H ℓ e γ i) = cls (GammaHUpper M H ℓ) (r M H ℓ e i * γ) := by
  rw [perm, Equiv.apply_symm_apply]

theorem r_mul_eq (γ : ↥(GammaH M H)) (i : ι) :
    r M H ℓ e i * γ = ((slip (GammaHUpper M H ℓ) (e i) γ : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) *
      r M H ℓ e (perm M H ℓ e γ i) := by
  show _ = rep _ (e i) * γ * (rep _ (cls _ (rep _ (e i) * γ)))⁻¹ * rep _ (e (perm M H ℓ e γ i))
  rw [e_perm, inv_mul_cancel_right]

theorem perm_injective [Finite ι] (γ : ↥(GammaH M H)) : Function.Injective (perm M H ℓ e γ) := by
  intro i j hij
  have h := congrArg e hij
  rw [e_perm, e_perm] at h

  have h' : cls (GammaHUpper M H ℓ) (r M H ℓ e i) = cls (GammaHUpper M H ℓ) (r M H ℓ e j) := by
    apply Quotient.sound
    have hr : QuotientGroup.rightRel (GammaHUpper M H ℓ) (r M H ℓ e i * γ) (r M H ℓ e j * γ) :=
      Quotient.exact h
    show QuotientGroup.rightRel (GammaHUpper M H ℓ) (r M H ℓ e i) (r M H ℓ e j)
    rw [QuotientGroup.rightRel_apply] at hr ⊢
    simpa [mul_assoc] using hr
  have hi : cls (GammaHUpper M H ℓ) (r M H ℓ e i) = e i := Quotient.out_eq' (e i)
  have hj : cls (GammaHUpper M H ℓ) (r M H ℓ e j) = e j := Quotient.out_eq' (e j)
  rw [hi, hj] at h'
  exact e.injective h'

theorem perm_bijective [Finite ι] (γ : ↥(GammaH M H)) : Function.Bijective (perm M H ℓ e γ) :=
  Finite.injective_iff_bijective.mp (perm_injective M H ℓ e γ)

variable [NeZero ℓ]

theorem beta_mul_mapGL (γ : ↥(GammaH M H)) (i : ι) :
    beta M H ℓ e i * Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) =
      Matrix.SpecialLinearGroup.mapGL ℝ
          ((conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ) : ↥(GammaH M H)) : SL(2, ℤ)) *
        beta M H ℓ e (perm M H ℓ e γ i) := by
  have hgrp : ((r M H ℓ e i : ↥(GammaH M H)) : SL(2, ℤ)) * (γ : SL(2, ℤ)) =
      (((slip (GammaHUpper M H ℓ) (e i) γ : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ)) *
        ((r M H ℓ e (perm M H ℓ e γ i) : ↥(GammaH M H)) : SL(2, ℤ)) := by
    have h := congrArg (fun x : ↥(GammaH M H) => (x : SL(2, ℤ))) (r_mul_eq M H ℓ e γ i)
    simpa only [Subgroup.coe_mul] using h
  rw [beta, beta, mul_assoc, ← map_mul, hgrp, map_mul, ← mul_assoc, alpha_mul_mapGL, mul_assoc]

variable {F : ℍ → ℂ}

theorem apply_beta_smul (hF : ModularCurve.Period.IsEquivariantPrimitive (GammaH M H) F)
    (γ : ↥(GammaH M H)) (i : ι) (z : ℍ) :
    F (beta M H ℓ e i • ((γ : SL(2, ℤ)) • z)) =
      F (beta M H ℓ e (perm M H ℓ e γ i) • z) +
        hF.period (conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ)) := by
  have h1 : beta M H ℓ e i • ((γ : SL(2, ℤ)) • z) =
      ((conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ) : ↥(GammaH M H)) : SL(2, ℤ)) •
        (beta M H ℓ e (perm M H ℓ e γ i) • z) := by
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, ← mul_smul, ← mul_smul]
    exact congrArg (· • z) (beta_mul_mapGL M H ℓ e γ i)
  rw [h1, ← hF.sub_eq_period (conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ))
    (beta M H ℓ e (perm M H ℓ e γ i) • z)]
  ring

theorem sum_apply_beta_smul_sub [Fintype ι]
    (hF : ModularCurve.Period.IsEquivariantPrimitive (GammaH M H) F) (γ : ↥(GammaH M H)) (z : ℍ) :
    (∑ i, F (beta M H ℓ e i • ((γ : SL(2, ℤ)) • z))) - ∑ i, F (beta M H ℓ e i • z) =
      ∑ i, hF.period (conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ)) := by
  simp_rw [apply_beta_smul M H ℓ e hF γ]
  rw [Finset.sum_add_distrib]
  have hperm : ∑ i, F (beta M H ℓ e (perm M H ℓ e γ i) • z) = ∑ i, F (beta M H ℓ e i • z) :=
    Function.Bijective.sum_comp (perm_bijective M H ℓ e γ) (fun i => F (beta M H ℓ e i • z))
  rw [hperm]
  ring

end Transversal

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {ι : Type*} [Fintype ι]
  (e : ι ≃ Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)))

theorem periodMapOf_eq_heckeT_of_coe_eq_sum (f g : CuspForm (GammaH M H) 2)
    (hg : ⇑g = ∑ i, (⇑f) ∣[(2 : ℤ)] beta M H ℓ e i) :
    ModularCurve.periodMapOf (GammaH M H) g =
      heckeT M H ℓ ℂ (ModularCurve.periodMapOf (GammaH M H) f) := by
  classical

  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf (GammaH M H) f
  have hder : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ := hF.1
  have hequiv : ModularCurve.Period.IsEquivariantPrimitive (GammaH M H) F := hF.2.2.1

  set G : ℍ → ℂ := fun z => ∑ i, F (beta M H ℓ e i • z) with hG
  have hderG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ := by
    intro τ
    rw [hg, Finset.sum_apply]
    have hfun : G ∘ ofComplex = fun z : ℂ => ∑ i, F (beta M H ℓ e i • ofComplex z) := by
      funext z; simp only [hG, Function.comp_apply]
    rw [hfun]
    exact HasDerivAt.fun_sum fun i _ => hasDerivAt_comp_smul hder (det_beta_pos M H ℓ e i) τ

  refine AddMonoidHom.ext fun a => ?_
  set γ := Additive.toMul a
  have ha : a = Additive.ofMul γ := rfl
  rw [ha, ModularCurve.periodMapOf_apply_eq_periodOf, ModularCurve.periodOf,
    periodAlongOf_eq_sub (GammaH M H) _ hderG,
    heckeT_apply_eq_sumEquiv M H ℓ e (ModularCurve.periodMapOf (GammaH M H) f) γ]
  have hL : G ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - G UpperHalfPlane.I =
      ∑ i, hequiv.period (conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ)) :=
    sum_apply_beta_smul_sub M H ℓ e hequiv γ UpperHalfPlane.I
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModularCurve.periodMapOf_apply_eq_periodOf,
    ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (GammaH M H) f hF]
  rfl

end Main

section Uq

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

theorem alpha_mul_mapGL_uMat (t : ℕ) :
    alpha q * Matrix.SpecialLinearGroup.mapGL ℝ (uMat (t : ℤ)) = ModularForm.heckeMatrix q t := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply, mapGL_apply]
  fin_cases i <;> fin_cases j <;> simp [ModularForm.val_heckeMatrix (NeZero.ne q), uMat]

theorem slash_alpha_rep_cls (k : ℤ) (f : CuspForm (GammaH M H) k) (x : ↥(GammaH M H)) :
    (⇑f) ∣[k] (alpha q * Matrix.SpecialLinearGroup.mapGL ℝ
        ((rep (GammaHUpper M H q) (cls (GammaHUpper M H q) x) : ↥(GammaH M H)) : SL(2, ℤ))) =
      (⇑f) ∣[k] (alpha q * Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ))) := by

  have hrel : QuotientGroup.rightRel (GammaHUpper M H q) (rep (GammaHUpper M H q) (cls _ x)) x :=
    Quotient.exact (Quotient.out_eq' (cls (GammaHUpper M H q) x))
  rw [QuotientGroup.rightRel_apply] at hrel
  set δ : ↥(GammaHUpper M H q) := ⟨x * (rep (GammaHUpper M H q) (cls _ x))⁻¹, hrel⟩ with hδ
  have hx : (rep (GammaHUpper M H q) (cls _ x) : ↥(GammaH M H)) =
      ((δ⁻¹ : ↥(GammaHUpper M H q)) : ↥(GammaH M H)) * x := by
    rw [InvMemClass.coe_inv, hδ]
    group
  rw [hx, Subgroup.coe_mul, map_mul, ← mul_assoc, alpha_mul_mapGL, mul_assoc, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (conjL M H q δ⁻¹).2)]

theorem sum_zmod_val {A : Type*} [AddCommMonoid A] (φ : ℕ → A) :
    ∑ j : ZMod q, φ j.val = ∑ n ∈ Finset.range q, φ n := by
  refine Finset.sum_nbij' (fun j => j.val) (fun n => (n : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.2 (ZMod.val_lt j)
  · intro n _; exact Finset.mem_univ _
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro n hn; exact ZMod.val_natCast_of_lt (Finset.mem_range.1 hn)
  · intro j _; rfl

theorem sum_slash_beta_eq_heckeU (hqM : q ∣ M) (k : ℤ) (f : CuspForm (GammaH M H) k) :
    ∑ j : ZMod q, (⇑f) ∣[k] beta M H q (rightQuotEquivOfDvd M H q hqM) j = ModularForm.heckeU k q ⇑f := by
  rw [ModularForm.heckeU_def, ← sum_zmod_val q (fun n => (⇑f) ∣[k] ModularForm.heckeMatrix q n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [beta, r, rightQuotEquivOfDvd_apply]
  show (⇑f) ∣[k] (alpha q * Matrix.SpecialLinearGroup.mapGL ℝ
      ((rep (GammaHUpper M H q) (cls (GammaHUpper M H q) (uElt M H (j.val : ℤ))) : ↥(GammaH M H)) :
        SL(2, ℤ))) = _
  rw [slash_alpha_rep_cls, coe_uElt, alpha_mul_mapGL_uMat]

variable [NeZero M]

theorem periodMapOf_eq_heckeT_of_coe_eq_heckeU (hqM : q ∣ M) (f g : CuspForm (GammaH M H) 2)
    (hg : ⇑g = ModularForm.heckeU 2 q ⇑f) :
    ModularCurve.periodMapOf (GammaH M H) g = heckeT M H q ℂ (ModularCurve.periodMapOf (GammaH M H) f) :=
  periodMapOf_eq_heckeT_of_coe_eq_sum M H q (rightQuotEquivOfDvd M H q hqM) f g
    (by rw [hg, sum_slash_beta_eq_heckeU])

end Uq

section StableU

theorem heckeMatrix_mul_heckeMatrix {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (j i : ℕ) :
    ModularForm.heckeMatrix m j * ModularForm.heckeMatrix n i = ModularForm.heckeMatrix (m * n) (i + j * n) := by
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;>
    simp [ModularForm.val_heckeMatrix hm, ModularForm.val_heckeMatrix hn,
      ModularForm.val_heckeMatrix (mul_ne_zero hm hn)]

theorem sum_slash {α : Type*} (s : Finset α) (F : α → ℍ → ℂ) (k : ℤ) (A : GL (Fin 2) ℝ) :
    (∑ a ∈ s, F a) ∣[k] A = ∑ a ∈ s, F a ∣[k] A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

theorem heckeU_heckeU (k : ℤ) (m n : ℕ) (F : ℍ → ℂ) :
    ModularForm.heckeU k n (ModularForm.heckeU k m F) = ModularForm.heckeU k (m * n) F := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ModularForm.heckeU_def, ModularForm.heckeU_def, ModularForm.heckeU_def]
  simp_rw [sum_slash, ← SlashAction.slash_mul, heckeMatrix_mul_heckeMatrix hm hn]

  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun t => (t % n, t / n)) (fun p => p.1 + p.2 * n) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_range] at ht
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hn), Nat.div_lt_of_lt_mul (by rwa [mul_comm] at ht)⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_range]
    calc p.1 + p.2 * n < n + p.2 * n := by omega
      _ = (p.2 + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right _ hp.2
  · intro t _
    simp only
    exact Nat.mod_add_div' t n
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    ext
    · simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp.1]
    · simp [Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero hn), Nat.div_eq_of_lt hp.1]
  · intro t _
    simp only [Nat.mod_add_div' t n]

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)

theorem stableU_one : CuspForm.StableU M H k 1 := by
  intro f
  have h1 : ModularForm.heckeU k 1 ⇑f = ⇑f := by
    rw [ModularForm.heckeU_def, Finset.sum_range_one]
    have : ModularForm.heckeMatrix 1 0 = 1 := by
      refine Matrix.GeneralLinearGroup.ext fun a b => ?_
      fin_cases a <;> fin_cases b <;> simp
    rw [this, SlashAction.slash_one]
  rw [h1]
  exact ⟨fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ, f.holo',
    fun c hc => CuspFormClass.zero_at_cusps f hc⟩

theorem stableU_mul {m n : ℕ} (hm : CuspForm.StableU M H k m) (hn : CuspForm.StableU M H k n) :
    CuspForm.StableU M H k (m * n) := by
  intro f
  set G : CuspForm (GammaH M H) k := CuspForm.heckeULinH k n (CuspForm.heckeULinH k m f) with hG
  have hcoe : ModularForm.heckeU k (m * n) ⇑f = ⇑G := by
    rw [hG, CuspForm.coe_heckeULinH_apply k hn, CuspForm.coe_heckeULinH_apply k hm, heckeU_heckeU]
  rw [hcoe]
  exact ⟨fun γ hγ => SlashInvariantFormClass.slash_action_eq G γ hγ, G.holo',
    fun c hc => CuspFormClass.zero_at_cusps G hc⟩

theorem stableU_of_dvd : ∀ {q : ℕ}, q ∣ M → CuspForm.StableU M H k q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hqM
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q
      · exact absurd (zero_dvd_iff.mp hqM) (NeZero.ne M)
      · exact stableU_one M H k
    · have hp : q.minFac.Prime := Nat.minFac_prime (by omega)
      have hpq : q.minFac ∣ q := Nat.minFac_dvd q
      obtain ⟨m, hm⟩ := hpq
      have hmq : m < q := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hm; omega
        · calc m < q.minFac * m := lt_mul_left h0 hp.one_lt
            _ = q := hm.symm
      have hmM : m ∣ M := dvd_trans (Dvd.intro_left _ hm.symm) hqM
      have hpM : q.minFac ∣ M := dvd_trans ⟨m, hm⟩ hqM
      rw [hm, mul_comm]
      exact stableU_mul M H k (ih m hmq hmM) (CuspForm.stableU M H k hp hpM)

end StableU

end PerU

section Group

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem Gamma_le_gammaH : Gamma M ≤ GammaH M H := by
  intro A hA
  rw [Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  have hA0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact h10
  rw [mem_GammaH_iff]
  refine ⟨hA0, ?_⟩
  have h1 : gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [h1]
  exact one_mem H

theorem isCongruenceSubgroup [NeZero M] : IsCongruenceSubgroup (GammaH M H) :=
  ⟨M, NeZero.ne M, Gamma_le_gammaH M H⟩

private scoped instance _root_.EsUPar.finiteIndex [NeZero M] : (GammaH M H).FiniteIndex := (isCongruenceSubgroup M H).finiteIndex

p2m_export "EsUPar" "finiteIndex"
end Group

section Phi

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "Γ" => GammaH M H

abbrev per (f : CuspForm Γ 2) : Additive ↥Γ →+ ℂ := periodMapOf Γ f

def cj (ψ : Additive ↥Γ →+ ℂ) : Additive ↥Γ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom.comp ψ

omit [NeZero M] in
@[scoped simp] theorem cj_apply (ψ : Additive ↥Γ →+ ℂ) (x : Additive ↥Γ) : cj M H ψ x = conj (ψ x) := rfl

omit [NeZero M] in
theorem cj_add (ψ ψ' : Additive ↥Γ →+ ℂ) : cj M H (ψ + ψ') = cj M H ψ + cj M H ψ' := by
  refine AddMonoidHom.ext fun x => ?_
  simp

omit [NeZero M] in
theorem cj_smul (c : ℂ) (ψ : Additive ↥Γ →+ ℂ) : cj M H (c • ψ) = conj c • cj M H ψ := by
  refine AddMonoidHom.ext fun x => ?_
  simp

def Phi (f g : CuspForm Γ 2) : Additive ↥Γ →+ ℂ := per M H f + cj M H (per M H g)

omit [NeZero M] in
theorem Phi_def (f g : CuspForm Γ 2) :
    Phi M H f g = periodMapOf Γ f + (starRingEnd ℂ).toAddMonoidHom.comp (periodMapOf Γ g) := rfl

theorem per_apply (f : CuspForm Γ 2) (x : Additive ↥Γ) :
    per M H f x = periodOf Γ (Additive.toMul x) f :=
  periodMapOf_apply_eq_periodOf Γ f (Additive.toMul x)

theorem per_add (f g : CuspForm Γ 2) : per M H (f + g) = per M H f + per M H g := by
  refine AddMonoidHom.ext fun x => ?_
  simp only [AddMonoidHom.add_apply, per_apply, map_add]

theorem per_smul (c : ℂ) (f : CuspForm Γ 2) : per M H (c • f) = c • per M H f := by
  refine AddMonoidHom.ext fun x => ?_
  simp only [AddMonoidHom.smul_apply, per_apply, map_smul]

theorem per_zero : per M H (0 : CuspForm Γ 2) = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  simp only [per_apply, map_zero, AddMonoidHom.zero_apply]

theorem Phi_zero_zero : Phi M H 0 0 = 0 := by
  rw [Phi, per_zero]
  refine AddMonoidHom.ext fun x => ?_
  simp

omit [NeZero M] in
theorem Phi_mem (f g : CuspForm Γ 2) : Phi M H f g ∈ parabolicHoms ℂ Γ ℂ := by
  intro γ hγ
  have hf := periodMapOf_mem_parabolicHoms Γ f γ hγ
  have hg := periodMapOf_mem_parabolicHoms Γ g γ hγ
  show per M H f (Additive.ofMul γ) + conj (per M H g (Additive.ofMul γ)) = 0
  rw [show per M H f (Additive.ofMul γ) = 0 from hf, show per M H g (Additive.ofMul γ) = 0 from hg,
    map_zero, add_zero]

theorem Phi_injective {f g f' g' : CuspForm Γ 2} (h : Phi M H f g = Phi M H f' g') :
    f = f' ∧ g = g' := by
  have hu := existsUnique_periodMapOf_add_conj_periodMapOf_eq_of_mem_parabolicHoms Γ
    (isCongruenceSubgroup M H) (Phi M H f g) (Phi_mem M H f g)
  have e := hu.unique (y₁ := (f, g)) (y₂ := (f', g')) rfl (by rw [h]; rfl)
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

theorem smul_Phi (c : ℂ) (f g : CuspForm Γ 2) :
    c • Phi M H f g = Phi M H (c • f) (conj c • g) := by
  rw [Phi, Phi, smul_add, per_smul, per_smul, cj_smul, Complex.conj_conj]

theorem eigen_of_intertwine {P : CuspForm Γ 2 →ₗ[ℂ] CuspForm Γ 2} {A : (Additive ↥Γ →+ ℂ) →+ (Additive ↥Γ →+ ℂ)}
    (hP : ∀ f : CuspForm Γ 2, per M H (P f) = A (per M H f)) (hA : ∀ ψ, A (cj M H ψ) = cj M H (A ψ))
    {c : ℂ} {f g : CuspForm Γ 2} (h : A (Phi M H f g) = c • Phi M H f g) :
    P f = c • f ∧ P g = conj c • g := by
  have hAPhi : A (Phi M H f g) = Phi M H (P f) (P g) := by
    rw [Phi, Phi, map_add, hA, ← hP, ← hP]
  rw [hAPhi, smul_Phi] at h
  exact Phi_injective M H h

theorem per_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm Γ 2) :
    per M H (CuspForm.heckeTLinH 2 hℓ hℓM f) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ℂ (per M H f)) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 hℓ hℓM) f _
    (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

theorem per_heckeULinH {q : ℕ} [NeZero q] (hqM : q ∣ M) (f : CuspForm Γ 2) :
    per M H (CuspForm.heckeULinH 2 q f) = heckeT M H q ℂ (per M H f) :=
  PerU.periodMapOf_eq_heckeT_of_coe_eq_heckeU M H q hqM f _
    (CuspForm.coe_heckeULinH_apply 2 (PerU.stableU_of_dvd M H 2 hqM) f)

theorem per_diamondLinH (u : (ZMod M)ˣ) (f : CuspForm Γ 2) :
    per M H (CuspForm.diamondLinH 2 u f) = diamondL M H ℂ u (per M H f) :=
  periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash M H (CuspForm.gammaLift M u) f _
    (CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2) u f)

omit [NeZero M] in
theorem heckeT_cj (n : ℕ) [NeZero n] (ψ : Additive ↥Γ →+ ℂ) :
    heckeT M H n ℂ (cj M H ψ) = cj M H (heckeT M H n ℂ ψ) :=
  heckeT_comp_coeff M H n (starRingEnd ℂ).toAddMonoidHom ψ

omit [NeZero M] in
theorem diamondRaw_cj (σ : Gamma0 M) (ψ : Additive ↥Γ →+ ℂ) :
    diamondRaw M H ℂ σ (cj M H ψ) = cj M H (diamondRaw M H ℂ σ ψ) := rfl

theorem heckeT_eigen {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {c : ℂ} {f g : CuspForm Γ 2}
    (h : (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ℂ (Phi M H f g)) = c • Phi M H f g) :
    CuspForm.heckeTLinH 2 hℓ hℓM f = c • f ∧ CuspForm.heckeTLinH 2 hℓ hℓM g = conj c • g := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact eigen_of_intertwine M H (A := heckeT M H ℓ ℂ) (per_heckeTLinH M H hℓ hℓM) (heckeT_cj M H ℓ) h

theorem heckeU_eigen {q : ℕ} [NeZero q] (hqM : q ∣ M) {c : ℂ} {f g : CuspForm Γ 2}
    (h : heckeT M H q ℂ (Phi M H f g) = c • Phi M H f g) :
    CuspForm.heckeULinH 2 q f = c • f ∧ CuspForm.heckeULinH 2 q g = conj c • g :=
  eigen_of_intertwine M H (A := heckeT M H q ℂ) (per_heckeULinH M H hqM) (heckeT_cj M H q) h

theorem diamond_eigen {u : (ZMod M)ˣ} {c : ℂ} {f g : CuspForm Γ 2}
    (h : diamondL M H ℂ u (Phi M H f g) = c • Phi M H f g) :
    CuspForm.diamondLinH 2 u f = c • f ∧ CuspForm.diamondLinH 2 u g = conj c • g :=
  eigen_of_intertwine M H (A := (diamondL M H ℂ u).toAddMonoidHom) (per_diamondLinH M H u)
    (fun ψ => diamondRaw_cj M H _ ψ) h

end Phi

section Conj

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem conj_natCast_zpow (p : ℕ) (m : ℤ) : conj ((p : ℂ) ^ m) = (p : ℂ) ^ m := by
  rw [map_zpow₀, Complex.conj_natCast]

theorem conj_intCast (n : ℤ) : conj (n : ℂ) = n := map_intCast _ n

theorem conj_dirichlet [NeZero M] (ε : DirichletCharacter ℂ M) (a : ZMod M) :
    conj (ε a) = ε⁻¹ a := by
  have := MulChar.star_apply' ε a
  rwa [RCLike.star_def] at this

theorem conj_ite (P : Prop) [Decidable P] (a : ℂ) :
    conj (if P then a else 0) = if P then conj a else 0 := by
  split_ifs <;> simp

theorem conj_hecke_rel [NeZero M] (ε : DirichletCharacter ℂ M) (a : ℕ → ℂ) (p : ℕ) (lam : ℂ)
    (h : ∀ n : ℕ, a (p * n) + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then a (n / p) else 0) = lam * a n) (n : ℕ) :
    conj (a (p * n)) + ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then conj (a (n / p)) else 0) = conj lam * conj (a n) := by
  have := congrArg conj (h n)
  rw [map_add, map_mul, map_mul, map_mul, conj_dirichlet, conj_natCast_zpow, conj_ite] at this
  exact this

def conjNeg (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have := Matrix.det_fin_two γ.1
    rw [γ.2] at this
    linear_combination (-1 : ℤ) * this⟩

@[scoped simp] theorem conjNeg_apply_00 (γ : SL(2, ℤ)) : (conjNeg γ) 0 0 = γ 0 0 := rfl
@[scoped simp] theorem conjNeg_apply_01 (γ : SL(2, ℤ)) : (conjNeg γ) 0 1 = -γ 0 1 := rfl
@[scoped simp] theorem conjNeg_apply_10 (γ : SL(2, ℤ)) : (conjNeg γ) 1 0 = -γ 1 0 := rfl
@[scoped simp] theorem conjNeg_apply_11 (γ : SL(2, ℤ)) : (conjNeg γ) 1 1 = γ 1 1 := rfl

theorem conjNeg_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : conjNeg γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at hγ ⊢
  simp [hγ]

def negConj (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

@[scoped simp] theorem coe_negConj (τ : ℍ) : ((negConj τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

theorem coe_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

theorem coe_conjNeg_smul_negConj (γ : SL(2, ℤ)) (τ : ℍ) :
    ((conjNeg γ • negConj τ : ℍ) : ℂ) = -conj ((γ • τ : ℍ) : ℂ) := by
  rw [coe_sl_smul, coe_sl_smul, map_div₀]
  simp only [conjNeg_apply_00, conjNeg_apply_01, conjNeg_apply_10, conjNeg_apply_11, coe_negConj,
    Int.cast_neg, map_add, map_mul, conj_intCast]
  have e1 : ((γ 0 0 : ℤ) : ℂ) * -conj (τ : ℂ) + -((γ 0 1 : ℤ) : ℂ) =
      -(((γ 0 0 : ℤ) : ℂ) * conj (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ)) := by ring
  have e2 : -((γ 1 0 : ℤ) : ℂ) * -conj (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) =
      ((γ 1 0 : ℤ) : ℂ) * conj (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by ring
  rw [e1, e2, neg_div]

theorem hasNebentypus_inv_of_conj [NeZero M] {ε : DirichletCharacter ℂ M}
    {f f' : CuspForm (Γ₁ℝ M) k} (hf : CuspForm.HasNebentypus ε f)
    (hf' : ∀ τ τ' : ℍ, (τ' : ℂ) = -conj (τ : ℂ) → f' τ = conj (f τ')) :
    CuspForm.HasNebentypus ε⁻¹ f' := by
  intro γ hγ τ
  have h1 : f' (γ • τ) = conj (f (conjNeg γ • negConj τ)) :=
    hf' (γ • τ) (conjNeg γ • negConj τ) (coe_conjNeg_smul_negConj γ τ)
  have h2 := hf (conjNeg γ) (conjNeg_mem_Gamma0 hγ) (negConj τ)
  have h3 : f' τ = conj (f (negConj τ)) := hf' τ (negConj τ) rfl
  rw [h1, h2, map_mul, map_mul, conjNeg_apply_11, conjNeg_apply_10, conj_dirichlet, ← h3,
    map_zpow₀, map_add, map_mul]
  simp only [Int.cast_neg, map_neg, conj_intCast, coe_negConj, Complex.conj_conj,
    neg_mul_neg]

theorem isEigenformWith_inv_of_conj [NeZero M] {ε : DirichletCharacter ℂ M}
    {h h' : CuspForm (Γ₁ℝ M) k} (hh : CuspForm.IsEigenformWith ε h)
    (hpt : ∀ τ τ' : ℍ, (τ' : ℂ) = -conj (τ : ℂ) → h' τ = conj (h τ'))
    (hcoef : ∀ n : ℕ, qCoeff h' n = conj (qCoeff h n)) :
    CuspForm.IsEigenformWith ε⁻¹ h' := by
  refine ⟨?_, ?_, ?_, hasNebentypus_inv_of_conj hh.hasNebentypus hpt⟩
  · rw [hcoef, hh.qCoeff_one, map_one]
  · intro p hp hpM n
    have := conj_hecke_rel (k := k) ε (fun n => qCoeff h n) p (qCoeff h p)
      (hh.hecke_of_not_dvd hp hpM) n
    beta_reduce at this
    rw [hcoef, hcoef, hcoef, hcoef]
    exact this
  · intro ℓ hℓ hℓM n
    rw [hcoef, hcoef, hcoef, hh.hecke_of_dvd hℓ hℓM n, map_mul]

end Conj

section Main

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def conjChar (e : (ZMod M)ˣ →* ℂˣ) : (ZMod M)ˣ →* ℂˣ :=
  (Units.map ((starRingEnd ℂ : ℂ →+* ℂ) : ℂ →* ℂ)).comp e

@[scoped simp] theorem coe_conjChar (e : (ZMod M)ˣ →* ℂˣ) (u : (ZMod M)ˣ) :
    ((conjChar M e u : ℂˣ) : ℂ) = conj ((e u : ℂˣ) : ℂ) := by
  simp [conjChar]

variable [NeZero M]

theorem main (S : Set ℕ) (Q : Set ℕ) (hQ : ∀ q ∈ Q, q ∣ M)
    (φ : H1 M H ℂ) (hφpar : φ ∈ parabolicHoms ℂ (GammaH M H) ℂ) (hφ0 : φ ≠ 0)
    (a b : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hU : ∀ (q : ℕ) (hq : q ∈ Q),
      (haveI : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne M) (hQ q hq)⟩;
        heckeT M H q ℂ φ) = b q • φ)
    (hD : ∀ u : (ZMod M)ˣ, diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ (ε : DirichletCharacter ℂ M) (h : CuspForm (Gamma1 M) 2),
      CuspForm.IsEigenformWith ε h ∧
      (∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → qCoeff h ℓ = a ℓ) ∧
      (∀ q ∈ Q, qCoeff h q = b q) := by

  obtain ⟨⟨f, g⟩, hfg, -⟩ :=
    existsUnique_periodMapOf_add_conj_periodMapOf_eq_of_mem_parabolicHoms (GammaH M H)
      (isCongruenceSubgroup M H) φ hφpar
  have hφ : φ = Phi M H f g := hfg.symm

  have hTf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (hℓM : ¬ ℓ ∣ M),
      CuspForm.heckeTLinH 2 hℓ hℓM f = a ℓ • f ∧ CuspForm.heckeTLinH 2 hℓ hℓM g = conj (a ℓ) • g := by
    intro ℓ hℓ hℓS hℓM
    have h := hT ℓ hℓ hℓS hℓM
    rw [hφ] at h
    exact heckeT_eigen M H hℓ hℓM h
  have hUf : ∀ (q : ℕ) (hq : q ∈ Q),
      CuspForm.heckeULinH 2 q f = b q • f ∧ CuspForm.heckeULinH 2 q g = conj (b q) • g := by
    intro q hq
    haveI : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne M) (hQ q hq)⟩
    have h := hU q hq
    rw [hφ] at h
    exact heckeU_eigen M H (hQ q hq) h
  have hDf : ∀ u : (ZMod M)ˣ, CuspForm.diamondLinH 2 u f = (e u : ℂ) • f ∧
      CuspForm.diamondLinH 2 u g = conj (e u : ℂ) • g := by
    intro u
    have h := hD u
    rw [hφ] at h
    exact diamond_eigen M H h
  by_cases hf0 : f = 0
  ·
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hφ0 (by rw [hφ, hf0, Phi_zero_zero])
    obtain ⟨ε', h', heig', hε', ha', hb'⟩ :=
      CuspForm.exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
        M H 2 S Q hQ (fun n => conj (a n)) (fun n => conj (b n)) (conjChar M e) g hg0
        (fun ℓ hℓ hℓS hℓM => (hTf ℓ hℓ hℓS hℓM).2) (fun q hq => (hUf q hq).2)
        (fun u => by rw [(hDf u).2, coe_conjChar])
    obtain ⟨h'', hpt, hcoef⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M 2 h'
    refine ⟨ε'⁻¹, h'', isEigenformWith_inv_of_conj heig' hpt hcoef, fun u => ?_,
      fun ℓ hℓ hℓS hℓM => ?_, fun q hq => ?_⟩
    · rw [← conj_dirichlet, hε' u, coe_conjChar, Complex.conj_conj]
    · rw [hcoef, ha' ℓ hℓ hℓS hℓM, Complex.conj_conj]
    · rw [hcoef, hb' q hq, Complex.conj_conj]
  ·
    exact CuspForm.exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
      M H 2 S Q hQ a b e f hf0 (fun ℓ hℓ hℓS hℓM => (hTf ℓ hℓ hℓS hℓM).1) (fun q hq => (hUf q hq).1)
      (fun u => (hDf u).1)

end Main

end EsUPar
p2m_reactivate "P2MW.S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul.EsUPar"

end
p2m_reactivate "P2MW.S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul.EsUPar"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (Q : Set ℕ) (hQ : ∀ q ∈ Q, q ∣ M)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) (hφ0 : φ ≠ 0)
    (a b : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hU : ∀ (q : ℕ) (hq : q ∈ Q),
      (haveI : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne M) (hQ q hq)⟩;
        CohCarrier.heckeT M H q ℂ φ) = b q • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ (ε : DirichletCharacter ℂ M) (h : CuspForm (CongruenceSubgroup.Gamma1 M) 2),
      CuspForm.IsEigenformWith ε h ∧
      (∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → ModularFormClass.qCoeff h ℓ = a ℓ) ∧
      (∀ q ∈ Q, ModularFormClass.qCoeff h q = b q) :=
  EsUPar.main M H S Q hQ φ hφpar hφ0 a b e hT hU hD

end S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul
end P2MW
export P2MW.S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul (solution)
