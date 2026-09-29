-- Prove2me | solution 1 for CuspForm.mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/43af1fc2-da87-578f-81db-c9f94af8dbbc

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_CuspForm_exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH
import Theorems.Thm_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_qCoeff_slash_mem_range_of_mem_Gamma0_of_forall_qCoeff_mem_range
import Theorems.Thm_CuspForm_qCoeff_heckeU_add_slash_mem_range_of_forall_qCoeff_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex Ihara.instGroupIharaAmalgam ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup"
p2m_attr_erase "instance" "GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one"
p2m_attr_erase "simp" "Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace RATUqT

section Period

theorem T_mem_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T]
  refine ⟨hT0, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    simp [CongruenceSubgroup.Gamma0Map, ModularGroup.coe_T]
  rw [h1]
  exact one_mem H

theorem one_mem_strictPeriods (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

end Period

section Rat

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

omit [NeZero M] in

theorem mem_range_iff (x : ℂ) : x ∈ (algebraMap ℚ ℂ).range ↔ ∃ r : ℚ, x = (r : ℂ) := by
  rw [RingHom.mem_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, eq_ratCast _ r⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, eq_ratCast _ r⟩

def IsRat (g : CuspForm (CohCarrier.GammaH M H) k) : Prop :=
  ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n ∈ (algebraMap ℚ ℂ).range

theorem isRat_zero : IsRat (0 : CuspForm (CohCarrier.GammaH M H) k) := by
  intro n
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
  exact Subring.zero_mem _

theorem isRat_add {f g : CuspForm (CohCarrier.GammaH M H) k} (hf : IsRat f) (hg : IsRat g) :
    IsRat (f + g) := by
  intro n
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M H) f g, map_add]
  exact Subring.add_mem _ (hf n) (hg n)

theorem isRat_neg {f : CuspForm (CohCarrier.GammaH M H) k} (hf : IsRat f) : IsRat (-f) := by
  intro n
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_neg, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods M H) f, map_neg]
  exact Subring.neg_mem _ (hf n)

theorem isRat_heckeGenH (x : CohCarrier.Gen M (∅ : Set ℕ)) {f : CuspForm (CohCarrier.GammaH M H) k}
    (hf : IsRat f) : IsRat (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) k x f) := by
  cases x with
  | T ℓ hℓ hℓS hℓM =>
    show IsRat (CuspForm.heckeTLinH k hℓ hℓM f)
    by_cases hT : CuspForm.StableT M H k ℓ
    · intro n
      rw [CuspForm.coe_heckeTLinH_apply k hℓ hℓM hT f]
      exact CuspForm.qCoeff_heckeU_add_slash_mem_range_of_forall_qCoeff_mem_range M H k hℓ hℓM
        _ (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)).2
        (CuspForm.gammaLift_apply_11 hℓ hℓM) f hf n
    · have h0 : (CuspForm.heckeTLinH k hℓ hℓM :
          CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k) = 0 :=
        dif_neg hT
      rw [h0, LinearMap.zero_apply]
      exact isRat_zero
  | U q hq hqM =>
    show IsRat (CuspForm.heckeULinH k q f)
    by_cases hU : CuspForm.StableU M H k q
    · intro n
      rw [CuspForm.coe_heckeULinH_apply k hU f,
        ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods M H) hq.ne_zero n,
        ModularForm.coeffHeckeU_apply]
      exact hf _
    · have h0 : (CuspForm.heckeULinH k q :
          CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k) = 0 :=
        dif_neg hU
      rw [h0, LinearMap.zero_apply]
      exact isRat_zero
  | dia d =>
    show IsRat (CuspForm.diamondLinH k d f)
    by_cases hD : CuspForm.StableD M H k
    · intro n
      rw [CuspForm.coe_diamondLinH_apply k hD d f]
      exact CuspForm.qCoeff_slash_mem_range_of_mem_Gamma0_of_forall_qCoeff_mem_range M H k f hf
        _ (CuspForm.gammaLift M d).2 n
    · have h0 : (CuspForm.diamondLinH k d :
          CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k) = 0 :=
        dif_neg hD
      rw [h0, LinearMap.zero_apply]
      exact isRat_zero

theorem isRat_apply_of_mem_closure
    {t : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k}
    (ht : t ∈ Subring.closure (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) k)))
    (f : CuspForm (CohCarrier.GammaH M H) k) (hf : IsRat f) : IsRat (t f) := by
  induction ht using Subring.closure_induction generalizing f with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact isRat_heckeGenH y hf
  | zero =>
    intro n
    exact isRat_zero (M := M) (H := H) (k := k) n
  | one => exact hf
  | add s s' _ _ hs hs' =>
    rw [LinearMap.add_apply]
    exact isRat_add (hs f hf) (hs' f hf)
  | neg s _ hs =>
    rw [LinearMap.neg_apply]
    exact isRat_neg (hs f hf)
  | mul s s' _ _ hs hs' => exact hs _ (hs' f hf)

theorem isRat_apply_of_mem_heckeRingH
    {t : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k}
    (ht : t ∈ CuspForm.heckeRingH M H k)
    (f : CuspForm (CohCarrier.GammaH M H) k) (hf : IsRat f) : IsRat (t f) :=
  isRat_apply_of_mem_closure ht f hf

end Rat

end RATUqT

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (algebraMap ℚ ℂ).range)
    (Y : CuspForm (CohCarrier.GammaH M H) 2)
    (hY : ⇑Y = ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) :
    Y ∈ CuspForm.twoCuspIntegralSet M H 2 p (algebraMap ℚ ℂ).range := by

  have hR : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro h
    apply hpM2
    rw [pow_two, hR]
    exact Nat.mul_dvd_mul_left p h
  have hbez : ((p : ℤ) * Nat.gcdA p (M / p) - ((M / p : ℕ) : ℤ) * (-Nat.gcdB p (M / p))) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p (M / p)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at h
    linear_combination -h
  let W₀ : ModularForm.AtkinLehnerDatum M p :=
    { R := M / p, hM := hR, a := Nat.gcdA p (M / p), b := -Nat.gcdB p (M / p), bezout := hbez }

  have hfR : RATUqT.IsRat f := by
    intro n
    have h := ((CuspForm.mem_twoCuspIntegralSet_iff f).mp hf 1
      (Subring.one_mem (CuspForm.heckeRingH M H 2)) W₀ n).1
    simpa only [Module.End.one_apply] using h

  have hYR : RATUqT.IsRat Y := by
    intro n
    rw [hY]
    exact CuspForm.qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
      M H q hq hqM 2 f hfR n

  rw [CuspForm.mem_twoCuspIntegralSet_iff]
  intro t ht W n
  have htY : RATUqT.IsRat (t Y) := RATUqT.isRat_apply_of_mem_heckeRingH ht Y hYR
  refine ⟨htY n, ?_⟩
  obtain ⟨r, hr⟩ := CuspForm.exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH p M hpM H hHp W
    (t Y) (fun m => (RATUqT.mem_range_iff _).mp (htY m)) n
  rw [hr]
  exact (RATUqT.mem_range_iff _).mpr ⟨r, rfl⟩

end S_CuspForm_mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range
end P2MW
export P2MW.S_CuspForm_mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range (solution)
