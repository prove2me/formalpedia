-- Prove2me | solution 1 for CohCarrier.exists_primitive_mem_parabolicHoms_heckeT_eq_smul_level_mul_of_heckeTLin_eq_smul_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c9425e3d-ef46-57e2-b60e-f80c38d74db9

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_PeriodHomPair
import Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_gammaH
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_heckeT_mem_parabolicHoms
import Theorems.Thm_CohCarrier_opFamily_apply_mem_parabolicHoms_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_primitive_mem_parabolicHoms_heckeT_eq_smul_level_mul_of_heckeTLin_eq_smul_of_notMem
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

noncomputable section

namespace CohCarrier
p2m_export "CohCarrier" "Gen heckeTL diamondL Gen.dia GammaH GammaH_le_Gamma0 H1 heckeT exists_eichlerShimura_H1_gammaH heckeT_comp_coeff heckeT_mem_parabolicHoms opFamily_apply_mem_parabolicHoms_gammaH"
namespace O3Prim
p2m_open "CohCarrier"

p2m_open "CohCarrier P2MW.S_CohCarrier_exists_primitive_mem_parabolicHoms_heckeT_eq_smul_level_mul_of_heckeTLin_eq_smul_of_notMem.CohCarrier ModularCurve.Period"
open scoped MatrixGroups ModularForm

section Complex

variable (N : ℕ) [NeZero N] (r : ℕ) [NeZero (N * r)] (H : Subgroup (ZMod (N * r))ˣ)

omit [NeZero N] [NeZero (N * r)] in
private theorem gamma0_mul_le : CongruenceSubgroup.Gamma0 (N * r) ≤ CongruenceSubgroup.Gamma0 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right N r)).trans hγ

omit [NeZero N] [NeZero (N * r)] in
private theorem gammaH_le : CohCarrier.GammaH (N * r) H ≤ CongruenceSubgroup.Gamma0 N :=
  fun _ hγ => gamma0_mul_le N r (CohCarrier.GammaH_le_Gamma0 H hγ)

private def liftForm (g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    CuspForm (CohCarrier.GammaH (N * r) H) 2 where
  toFun := g'
  slash_action_eq' γ hγ :=
    SlashInvariantFormClass.slash_action_eq g' γ (Subgroup.map_mono (gammaH_le N r H) hγ)
  holo' := CuspFormClass.holo g'
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps g' (hc.mono (Subgroup.map_mono (gammaH_le N r H)))

private theorem coe_liftForm (g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    (⇑(liftForm N r H g') : UpperHalfPlane → ℂ) = ⇑g' := rfl

omit [NeZero N] [NeZero (N * r)] in
private theorem slash_of_mem_gamma0_mul (g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N * r)) :
    (⇑g' : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g' :=
  SlashInvariantFormClass.slash_action_eq g' _ (Subgroup.mem_map_of_mem _ (gamma0_mul_le N r hγ))

set_option maxHeartbeats 3200000 in

private theorem exists_eigenclass_complex
    (g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hg' : g' ≠ 0) (bC : ℕ → ℂ) (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g' = bC ℓ • g')
    (hU : ∀ (q : ℕ), q.Prime → ∀ (hqN : q ∣ N), CuspForm.heckeULin 2 hqN g' = bC q • g') :
    ∃ v : CohCarrier.H1 (N * r) H ℂ, v ≠ 0 ∧
      v ∈ parabolicHoms ℂ (CohCarrier.GammaH (N * r) H) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * r → ℓ ∉ S → haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        CohCarrier.heckeT (N * r) H ℓ ℂ v = bC ℓ • v) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ N → haveI : NeZero q := ⟨hq.ne_zero⟩;
        CohCarrier.heckeT (N * r) H q ℂ v = bC q • v) ∧
      (∀ d : (ZMod (N * r))ˣ, CohCarrier.diamondL (N * r) H ℂ d v = v) := by
  classical
  set F := liftForm N r H g' with hFdef
  have hF : (⇑F : UpperHalfPlane → ℂ) = ⇑g' := rfl
  have hF0 : F ≠ 0 := by
    intro h0
    apply hg'
    apply DFunLike.coe_injective
    change (⇑g' : UpperHalfPlane → ℂ) = ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    rw [← hF, h0]; rfl

  have hDF : ∀ d : (ZMod (N * r))ˣ, CuspForm.diamondLinH 2 d F = F := by
    intro d
    apply DFunLike.coe_injective
    change (⇑(CuspForm.diamondLinH 2 d F) : UpperHalfPlane → ℂ) = ⇑F
    rw [CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD (N * r) H 2) d F, hF]
    exact slash_of_mem_gamma0_mul N r g' (CuspForm.gammaLift (N * r) d).2

  have hTF : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * r), ℓ ∉ S →
      CuspForm.heckeTLinH 2 hℓ hℓM F = bC ℓ • F := by
    intro ℓ hℓ hℓM hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.mul_right r)
    apply DFunLike.coe_injective
    change (⇑(CuspForm.heckeTLinH 2 hℓ hℓM F) : UpperHalfPlane → ℂ) = ⇑(bC ℓ • F)
    rw [CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT (N * r) H 2 hℓ hℓM) F,
      CuspForm.IsGLPos.coe_smul, hF, SlashAction.slash_mul,
      slash_of_mem_gamma0_mul N r g' (CuspForm.gammaLift (N * r) _).2,
      ← ModularForm.heckeT_eq_heckeU_add, ← CuspForm.coe_heckeTLin_apply 2 hℓ hℓN g', hT ℓ hℓ hℓN hℓS,
      CuspForm.IsGLPos.coe_smul]

  have hUF : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
      CuspForm.heckeULinH 2 q F = bC q • F := by
    intro q hq hqN
    have hqM : q ∣ N * r := hqN.mul_right r
    apply DFunLike.coe_injective
    change (⇑(CuspForm.heckeULinH 2 q F) : UpperHalfPlane → ℂ) = ⇑(bC q • F)
    rw [CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU (N * r) H 2 hq hqM) F, CuspForm.IsGLPos.coe_smul, hF,
      ← CuspForm.coe_heckeULin_apply 2 hqN g', hU q hq hqN, CuspForm.IsGLPos.coe_smul]

  obtain ⟨J, ES, -, -, hinj, hrange, hEST, hESU, hESD⟩ := CohCarrier.exists_eichlerShimura_H1_gammaH (N * r) H
  have hsm : ∀ a : ℂ, ((a • F, 0) : CuspForm (CohCarrier.GammaH (N * r) H) 2 × CuspForm (CohCarrier.GammaH (N * r) H) 2)
      = a • (F, 0) := fun a => by rw [Prod.smul_mk, smul_zero]
  refine ⟨ES (F, 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro hv
    apply hF0
    have h0 : ((F, 0) : CuspForm (CohCarrier.GammaH (N * r) H) 2 × CuspForm (CohCarrier.GammaH (N * r) H) 2) = 0 :=
      hinj (by rw [hv, map_zero])
    exact (Prod.mk_eq_zero.mp h0).1
  · rw [← hrange]; exact LinearMap.mem_range_self ES _
  · intro ℓ hℓ hℓM hℓS
    have h1 := hEST ℓ hℓ hℓM F 0
    rw [map_zero, hTF ℓ hℓ hℓM hℓS, hsm, map_smul] at h1
    exact h1.symm
  · intro q hq hqN
    have h1 := hESU q hq (hqN.mul_right r) F 0
    rw [map_zero, hUF q hq hqN, hsm, map_smul] at h1
    exact h1.symm
  · intro d
    have h1 := hESD d F 0
    rw [map_zero, hDF d] at h1
    exact h1.symm

end Complex

section Transport

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

private abbrev PZ : Type := ↥(parabolicHoms ℤ (GammaH M H) ℤ)

private def _root_.CohCarrier.O3Prim.ext (R : Type) [CommRing R] : H1 M H ℤ →ₗ[ℤ] H1 M H R where
  toFun φ := (Int.castAddHom R).comp φ
  map_add' φ ψ := by ext; simp
  map_smul' n φ := by ext; simp

p2m_export "CohCarrier.O3Prim" "ext"
omit [NeZero M] in
private theorem ext_apply (R : Type) [CommRing R] (φ : H1 M H ℤ) : ext M H R φ = (Int.castAddHom R).comp φ := rfl

private def TZ (ℓ : ℕ) [NeZero ℓ] : Module.End ℤ (PZ M H) :=
  (heckeTL M H ℤ ℓ).restrict (fun φ hφ => heckeT_mem_parabolicHoms M H ℤ ℓ φ hφ)

private def DZ (d : (ZMod M)ˣ) : Module.End ℤ (PZ M H) :=
  (diamondL M H ℤ d).restrict
    (fun φ hφ => opFamily_apply_mem_parabolicHoms_gammaH M H (∅ : Set ℕ) ℤ (Gen.dia d) φ hφ)

variable {M H}
variable {n : ℕ} (bZ : Module.Basis (Fin n) ℤ (PZ M H))

omit [NeZero M] in

private theorem apply_sum_smul_eq {R : Type} [CommRing R] (O : H1 M H R →ₗ[R] H1 M H R) (f : Module.End ℤ (PZ M H))
    (hO : ∀ φ : PZ M H, O (ext M H R (φ : H1 M H ℤ)) = ext M H R ((f φ : PZ M H) : H1 M H ℤ))
    (bR : Fin n → H1 M H R) (hbR : ∀ i, bR i = (Int.castAddHom R).comp (bZ i : H1 M H ℤ))
    (x : Fin n → R) :
    O (∑ j, x j • bR j) = ∑ i, (∑ j, ((LinearMap.toMatrix bZ bZ f i j : ℤ) : R) * x j) • bR i := by
  classical
  have hOb : ∀ j, O (bR j) = ∑ i, ((LinearMap.toMatrix bZ bZ f i j : ℤ) : R) • bR i := by
    intro j
    rw [hbR j, ← ext_apply, hO, ← bZ.sum_repr (f (bZ j))]
    rw [show (((∑ i, (bZ.repr (f (bZ j))) i • bZ i : PZ M H)) : H1 M H ℤ) =
        ∑ i, (bZ.repr (f (bZ j))) i • ((bZ i : PZ M H) : H1 M H ℤ) from by
      rw [Submodule.coe_sum]; rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ext_apply, ← hbR i, LinearMap.toMatrix_apply, Int.cast_smul_eq_zsmul]
  rw [map_sum]
  simp_rw [map_smul, hOb, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

omit [NeZero M] in

private theorem heckeT_ext {R : Type} [CommRing R] (ℓ : ℕ) [NeZero ℓ] (φ : PZ M H) :
    heckeTL M H R ℓ (ext M H R (φ : H1 M H ℤ)) = ext M H R ((TZ M H ℓ φ : PZ M H) : H1 M H ℤ) :=
  heckeT_comp_coeff M H ℓ (Int.castAddHom R) (φ : H1 M H ℤ)

private theorem diamondL_ext {R : Type} [CommRing R] (d : (ZMod M)ˣ) (φ : PZ M H) :
    diamondL M H R d (ext M H R (φ : H1 M H ℤ)) = ext M H R ((DZ M H d φ : PZ M H) : H1 M H ℤ) := rfl

omit [NeZero M] in

private theorem coords_unique {R : Type} [CommRing R]
    (bR : Module.Basis (Fin n) R ↥(parabolicHoms R (GammaH M H) R)) (α β : Fin n → R)
    (h : (∑ i, α i • ((bR i : ↥(parabolicHoms R (GammaH M H) R)) : H1 M H R)) =
      ∑ i, β i • ((bR i : ↥(parabolicHoms R (GammaH M H) R)) : H1 M H R)) : α = β := by
  classical
  have h' : (((∑ i, α i • bR i : ↥(parabolicHoms R (GammaH M H) R))) : H1 M H R) =
      ((∑ i, β i • bR i : ↥(parabolicHoms R (GammaH M H) R)) : H1 M H R) := by
    rw [Submodule.coe_sum, Submodule.coe_sum]
    exact h
  have h'' : (∑ i, α i • bR i) = ∑ i, β i • bR i := Subtype.ext h'
  have := congrArg (fun v => (bR.repr v : Fin n →₀ R)) h''
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] at this
  funext i
  have hi := congrArg (fun f : Fin n →₀ R => f i) this
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hi
  exact hi

end Transport

section Descent

private theorem exists_ne_zero_solution_subfield {n : ℕ} (K : Subfield ℂ) {α : Type}
    (Mat : α → Matrix (Fin n) (Fin n) ℤ) (lam : α → ℂ) (hlam : ∀ a, lam a ∈ K)
    (x : Fin n → ℂ) (hx : x ≠ 0)
    (heq : ∀ a i, (∑ j, ((Mat a i j : ℤ) : ℂ) * x j) = lam a * x i) :
    ∃ y : Fin n → K, y ≠ 0 ∧ ∀ a i, (∑ j, ((Mat a i j : ℤ) : (K : Type)) * y j) = ⟨lam a, hlam a⟩ * y i := by
  classical
  let B := Module.Basis.ofVectorSpace K ℂ
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨β, hβ⟩ : ∃ β, B.repr (x j₀) β ≠ 0 := by
    by_contra h
    push Not at h
    apply hj₀
    have : B.repr (x j₀) = 0 := Finsupp.ext h
    exact B.repr.map_eq_zero_iff.mp this
  refine ⟨fun j => B.repr (x j) β, fun h0 => hβ (by simpa using congrFun h0 j₀), fun a i => ?_⟩

  have hlin : ∀ (c : K) (z : ℂ), B.repr ((c : ℂ) * z) β = c * B.repr z β := by
    intro c z
    rw [show (c : ℂ) * z = c • z from rfl, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have h1 := congrArg (fun z : ℂ => B.repr z β) (heq a i)
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply] at h1
  rw [show lam a * x i = ((⟨lam a, hlam a⟩ : K) : ℂ) * x i from rfl, hlin] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (((Mat a i j : ℤ) : ℂ)) = (((Mat a i j : ℤ) : K) : ℂ) from by push_cast; rfl, hlin]

private theorem exists_ne_zero_solution_subring {n : ℕ} (A : Subring ℂ) {α : Type}
    (Mat : α → Matrix (Fin n) (Fin n) ℤ) (lam : α → A)
    (x : Fin n → ℂ) (hx : x ≠ 0)
    (heq : ∀ a i, (∑ j, ((Mat a i j : ℤ) : ℂ) * x j) = ((lam a : A) : ℂ) * x i) :
    ∃ z : Fin n → A, z ≠ 0 ∧ ∀ a i, (∑ j, ((Mat a i j : ℤ) : A) * z j) = lam a * z i := by
  classical
  let K : Subfield ℂ := Subfield.closure (A : Set ℂ)
  have hAK : ∀ a : A, (a : ℂ) ∈ K := fun a => Subfield.subset_closure a.2
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_solution_subfield K Mat (fun a => ((lam a : A) : ℂ)) (fun a => hAK _) x hx heq

  have hfrac : ∀ j, ∃ p q : ℂ, p ∈ A ∧ q ∈ A ∧ q ≠ 0 ∧ (y j : ℂ) = p / q := by
    intro j
    have hmem : ((y j : K) : ℂ) ∈ Subfield.closure (A : Set ℂ) := (y j).2
    rw [Subfield.mem_closure_iff] at hmem
    obtain ⟨p, hp, q, hq, hpq⟩ := hmem
    rw [Subring.closure_eq] at hp hq
    by_cases hq0 : q = 0
    · refine ⟨0, 1, A.zero_mem, A.one_mem, one_ne_zero, ?_⟩
      rw [← hpq, hq0, div_zero, zero_div]
    · exact ⟨p, q, hp, hq, hq0, hpq.symm⟩
  choose p q hp hq hq0 hpq using hfrac
  let D : ℂ := ∏ j, q j
  have hD : D ∈ A := prod_mem (fun j _ => hq j)
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hq0 j
  have hzA : ∀ j, D * (y j : ℂ) ∈ A := by
    intro j
    rw [hpq j, show D = (∏ i ∈ Finset.univ.erase j, q i) * q j from
      (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm]
    rw [mul_assoc, mul_div_cancel₀ _ (hq0 j)]
    exact A.mul_mem (prod_mem fun i _ => hq i) (hp j)
  refine ⟨fun j => ⟨D * (y j : ℂ), hzA j⟩, ?_, fun a i => ?_⟩
  · intro h0
    apply hy0
    funext j
    have hj := congrArg (fun z : Fin n → A => ((z j : A) : ℂ)) h0
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at hj
    have : (y j : ℂ) = 0 := (mul_eq_zero.mp hj).resolve_left hD0
    exact Subtype.ext this
  · apply Subtype.ext
    have h1 := congrArg (fun c : K => D * (c : ℂ)) (hy a i)
    push_cast at h1 ⊢
    rw [Finset.mul_sum] at h1
    rw [show ((lam a : A) : ℂ) * (D * (y i : ℂ)) = D * (((lam a : A) : ℂ) * (y i : ℂ)) from by ring, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end Descent

section Primitive

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] {X : Type} [AddGroup X]

private theorem exists_primitive (φ : X →+ 𝒪') (hφ : φ ≠ 0) :
    ∃ (t : ℕ) (ϖ : 𝒪') (ψ : X →+ 𝒪'), ϖ ≠ 0 ∧ (∀ x, φ x = ϖ ^ t * ψ x) ∧ ∃ x₀, IsUnit (ψ x₀) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪'
  have hex : ∃ x, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (AddMonoidHom.ext h)
  let P : ℕ → Prop := fun m => ∃ x, ∃ u : 𝒪'ˣ, φ x = u * ϖ ^ m
  have hP : ∃ m, P m := by
    obtain ⟨x, hx⟩ := hex
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    exact ⟨m, x, u, hu⟩
  obtain ⟨x₀, u₀, hx₀⟩ : P (Nat.find hP) := Nat.find_spec hP
  have hdiv : ∀ x, ∃ c, φ x = ϖ ^ (Nat.find hP) * c := by
    intro x
    by_cases hx : φ x = 0
    · exact ⟨0, by rw [hx, mul_zero]⟩
    · obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
      have htm : Nat.find hP ≤ m := Nat.find_min' hP ⟨x, u, hu⟩
      refine ⟨u * ϖ ^ (m - Nat.find hP), ?_⟩
      rw [hu, mul_left_comm, ← pow_add, Nat.add_sub_cancel' htm]
  choose c hc using hdiv
  have hϖt : ϖ ^ (Nat.find hP) ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  refine ⟨Nat.find hP, ϖ, { toFun := c, map_zero' := ?_, map_add' := ?_ }, hϖ.ne_zero, hc, x₀, ?_⟩
  · apply mul_left_cancel₀ hϖt
    rw [← hc 0, map_zero, mul_zero]
  · intro x y
    apply mul_left_cancel₀ hϖt
    rw [← hc, map_add, hc x, hc y, mul_add]
  · show IsUnit (c x₀)
    have h1 : ϖ ^ (Nat.find hP) * c x₀ = ϖ ^ (Nat.find hP) * u₀ := by rw [← hc x₀, hx₀, mul_comm]
    rw [mul_left_cancel₀ hϖt h1]
    exact u₀.isUnit

omit [IsDiscreteValuationRing 𝒪'] in

private theorem smul_cancel {a : 𝒪'} (ha : a ≠ 0) {f g : X →+ 𝒪'} (h : a • f = a • g) : f = g := by
  refine AddMonoidHom.ext fun x => mul_left_cancel₀ ha ?_
  have := congrArg (fun φ : X →+ 𝒪' => φ x) h
  simpa [AddMonoidHom.smul_apply, smul_eq_mul] using this

end Primitive

section MainO3

set_option maxHeartbeats 6400000 in
private theorem main
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (N : ℕ) [NeZero N] (r : ℕ) [NeZero (N * r)]
    (H : Subgroup (ZMod (N * r))ˣ)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hg' : g' ≠ 0)
    (A : Subring ℂ) (ι : A →+* 𝒪') (hι : Function.Injective ι)
    (b : ℕ → A) (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g' = ((b ℓ : A) : ℂ) • g')
    (hU : ∀ (q : ℕ), q.Prime → ∀ (hqN : q ∣ N), CuspForm.heckeULin 2 hqN g' = ((b q : A) : ℂ) • g') :
    ∃ v : CohCarrier.H1 (N * r) H 𝒪',
      v ∉ ((IsLocalRing.maximalIdeal 𝒪') • ⊤ : Submodule 𝒪' (CohCarrier.H1 (N * r) H 𝒪')) ∧
      v ∈ parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪' ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * r → ℓ ∉ S → haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        CohCarrier.heckeT (N * r) H ℓ 𝒪' v = ι (b ℓ) • v) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ N → haveI : NeZero q := ⟨hq.ne_zero⟩;
        CohCarrier.heckeT (N * r) H q 𝒪' v = ι (b q) • v) ∧
      (∀ d : (ZMod (N * r))ˣ, CohCarrier.diamondL (N * r) H 𝒪' d v = v) := by
  classical

  obtain ⟨v, hv0, hvP, hvT, hvU, hvD⟩ :=
    exists_eigenclass_complex N r H g' hg' (fun m => ((b m : A) : ℂ)) S hT hU

  obtain ⟨n, bZ, hbR⟩ := exists_basis_parabolicHoms_of_isAddTorsionFree (CohCarrier.GammaH (N * r) H)
  obtain ⟨bC, hbC⟩ := hbR ℂ
  haveI : CharZero 𝒪' := by
    refine ⟨fun a a' h => ?_⟩
    have h1 : ι (a : A) = ι (a' : A) := by rw [map_natCast, map_natCast]; exact h
    have h2 : ((a : A) : ℂ) = ((a' : A) : ℂ) := congrArg (fun z : A => (z : ℂ)) (hι h1)
    push_cast at h2
    exact_mod_cast h2
  obtain ⟨bO, hbO⟩ := hbR 𝒪'

  set cv : ↥(parabolicHoms ℂ (CohCarrier.GammaH (N * r) H) ℂ) := ⟨v, hvP⟩ with hcv
  let x : Fin n → ℂ := fun j => bC.repr cv j
  have hvx : v = ∑ j, x j • ((bC j : ↥(parabolicHoms ℂ (CohCarrier.GammaH (N * r) H) ℂ)) : CohCarrier.H1 (N * r) H ℂ) := by
    have h1 : cv = ∑ j, x j • bC j := (bC.sum_repr cv).symm
    have h2 := congrArg (fun w : ↥(parabolicHoms ℂ (CohCarrier.GammaH (N * r) H) ℂ) => (w : CohCarrier.H1 (N * r) H ℂ)) h1
    rw [Submodule.coe_sum] at h2
    exact h2
  have hx0 : x ≠ 0 := by
    intro h0
    apply hv0
    rw [hvx]
    simp [h0]

  let α : Type := ({ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N * r ∧ ℓ ∉ S} ⊕ {q : ℕ // q.Prime ∧ q ∣ N}) ⊕ (ZMod (N * r))ˣ
  let fZ : α → Module.End ℤ (PZ (N * r) H) := fun a => match a with
    | Sum.inl (Sum.inl ℓ) => haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩; TZ (N * r) H ℓ.1
    | Sum.inl (Sum.inr q) => haveI : NeZero q.1 := ⟨q.2.1.ne_zero⟩; TZ (N * r) H q.1
    | Sum.inr d => DZ (N * r) H d
  let Mat : α → Matrix (Fin n) (Fin n) ℤ := fun a => LinearMap.toMatrix bZ bZ (fZ a)
  let lam : α → A := fun a => match a with
    | Sum.inl (Sum.inl ℓ) => b ℓ.1
    | Sum.inl (Sum.inr q) => b q.1
    | Sum.inr _ => 1

  let OR : ∀ (R : Type) [CommRing R], α → (CohCarrier.H1 (N * r) H R →ₗ[R] CohCarrier.H1 (N * r) H R) :=
    fun R _ a => match a with
    | Sum.inl (Sum.inl ℓ) => haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩; heckeTL (N * r) H R ℓ.1
    | Sum.inl (Sum.inr q) => haveI : NeZero q.1 := ⟨q.2.1.ne_zero⟩; heckeTL (N * r) H R q.1
    | Sum.inr d => diamondL (N * r) H R d
  have hOR : ∀ (R : Type) [CommRing R] (a : α) (φ : PZ (N * r) H),
      OR R a (ext (N * r) H R (φ : CohCarrier.H1 (N * r) H ℤ)) =
        ext (N * r) H R ((fZ a φ : PZ (N * r) H) : CohCarrier.H1 (N * r) H ℤ) := by
    intro R _ a φ
    rcases a with (ℓ | q) | d
    · haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
      exact heckeT_ext (M := N * r) (H := H) ℓ.1 φ
    · haveI : NeZero q.1 := ⟨q.2.1.ne_zero⟩
      exact heckeT_ext (M := N * r) (H := H) q.1 φ
    · exact diamondL_ext (M := N * r) (H := H) d φ

  have hvO : ∀ a : α, OR ℂ a v = ((lam a : A) : ℂ) • v := by
    intro a
    rcases a with (ℓ | q) | d
    · exact hvT ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2
    · exact hvU q.1 q.2.1 q.2.2
    · show diamondL (N * r) H ℂ d v = ((1 : A) : ℂ) • v
      rw [hvD d, OneMemClass.coe_one, one_smul]
  have heqC : ∀ (a : α) (i : Fin n), (∑ j, ((Mat a i j : ℤ) : ℂ) * x j) = ((lam a : A) : ℂ) * x i := by
    intro a
    have h1 := hvO a
    rw [hvx, apply_sum_smul_eq bZ (OR ℂ a) (fZ a) (hOR ℂ a) _ hbC x, Finset.smul_sum] at h1
    simp_rw [smul_smul] at h1
    exact fun i => congrFun (coords_unique bC _ _ h1) i

  obtain ⟨z, hz0, hz⟩ := exists_ne_zero_solution_subring A Mat lam x hx0 heqC

  let w : Fin n → 𝒪' := fun j => ι (z j)
  have hw0 : w ≠ 0 := by
    intro h0
    apply hz0
    funext j
    apply hι
    rw [Pi.zero_apply, map_zero]
    exact congrFun h0 j
  have heqO : ∀ (a : α) (i : Fin n), (∑ j, ((Mat a i j : ℤ) : 𝒪') * w j) = ι (lam a) * w i := by
    intro a i
    have h1 := congrArg ι (hz a i)
    rw [map_sum, map_mul] at h1
    simp_rw [map_mul, map_intCast] at h1
    exact h1

  let v₁ : CohCarrier.H1 (N * r) H 𝒪' :=
    ∑ j, w j • ((bO j : ↥(parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪')) : CohCarrier.H1 (N * r) H 𝒪')
  have hv₁P : v₁ ∈ parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪' :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bO j).2
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    apply hw0
    have h1 : (∑ j, w j • ((bO j : ↥(parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪')) : CohCarrier.H1 (N * r) H 𝒪'))
        = ∑ j, (0 : Fin n → 𝒪') j • ((bO j : ↥(parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪')) : CohCarrier.H1 (N * r) H 𝒪') := by
      rw [show (∑ j, w j • ((bO j : ↥(parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪')) : CohCarrier.H1 (N * r) H 𝒪')) = v₁ from rfl, h0]
      simp
    exact coords_unique bO _ _ h1
  have hv₁O : ∀ a : α, OR 𝒪' a v₁ = ι (lam a) • v₁ := by
    intro a
    show OR 𝒪' a (∑ j, w j • ((bO j : ↥(parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪')) : CohCarrier.H1 (N * r) H 𝒪')) = _
    rw [apply_sum_smul_eq bZ (OR 𝒪' a) (fZ a) (hOR 𝒪' a) _ hbO w, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heqO a i, smul_smul]

  obtain ⟨t, ϖ, ψ, hϖ0, hψ, x₀, hx₀⟩ := exists_primitive v₁ hv₁0
  have hϖt : ϖ ^ t ≠ 0 := pow_ne_zero _ hϖ0
  have hv₁ψ : v₁ = ϖ ^ t • ψ := AddMonoidHom.ext fun y => by rw [AddMonoidHom.smul_apply, smul_eq_mul]; exact hψ y
  have hψO : ∀ a : α, OR 𝒪' a ψ = ι (lam a) • ψ := by
    intro a
    apply smul_cancel hϖt
    rw [← map_smul, ← hv₁ψ, hv₁O a, hv₁ψ, smul_comm]
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hmem
    have hall : ∀ y, ψ y ∈ IsLocalRing.maximalIdeal 𝒪' := by
      refine Submodule.smul_induction_on (p := fun φ : CohCarrier.H1 (N * r) H 𝒪' => ∀ y, φ y ∈ IsLocalRing.maximalIdeal 𝒪')
        hmem ?_ ?_
      · intro c hc φ _ y
        rw [AddMonoidHom.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hc
      · intro φ₁ φ₂ h₁ h₂ y
        rw [AddMonoidHom.add_apply]
        exact Ideal.add_mem _ (h₁ y) (h₂ y)
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp (hall x₀))) hx₀
  ·
    rw [mem_parabolicHoms_iff] at hv₁P ⊢
    intro γ hγ
    have h1 := hv₁P γ hγ
    rw [hψ] at h1
    exact (mul_eq_zero.mp h1).resolve_left hϖt
  · intro ℓ hℓ hℓM hℓS
    exact hψO (Sum.inl (Sum.inl ⟨ℓ, hℓ, hℓM, hℓS⟩))
  · intro q hq hqN
    exact hψO (Sum.inl (Sum.inr ⟨q, hq, hqN⟩))
  · intro d
    have h1 := hψO (Sum.inr d)
    rw [show lam (Sum.inr d) = 1 from rfl, map_one, one_smul] at h1
    exact h1

end MainO3

end CohCarrier.O3Prim

end

open scoped MatrixGroups in
open IsLocalRing _root_.CohCarrier _root_.P2MW.S_CohCarrier_exists_primitive_mem_parabolicHoms_heckeT_eq_smul_level_mul_of_heckeTLin_eq_smul_of_notMem.CohCarrier in

theorem solution
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime) (hrN : ¬ r ∣ N) [NeZero (N * r)]
    (H : Subgroup (ZMod (N * r))ˣ)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hg' : g' ≠ 0)
    (A : Subring ℂ) (ι : A →+* 𝒪') (hι : Function.Injective ι)
    (b : ℕ → A)

    (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g' = ((b ℓ : A) : ℂ) • g')
    (hU : ∀ (q : ℕ), q.Prime → ∀ (hqN : q ∣ N), CuspForm.heckeULin 2 hqN g' = ((b q : A) : ℂ) • g') :
    ∃ v : CohCarrier.H1 (N * r) H 𝒪',
      v ∉ ((maximalIdeal 𝒪') • ⊤ : Submodule 𝒪' (CohCarrier.H1 (N * r) H 𝒪')) ∧
      v ∈ ModularCurve.Period.parabolicHoms 𝒪' (CohCarrier.GammaH (N * r) H) 𝒪' ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * r → ℓ ∉ S → haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        CohCarrier.heckeT (N * r) H ℓ 𝒪' v = ι (b ℓ) • v) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ N → haveI : NeZero q := ⟨hq.ne_zero⟩;
        CohCarrier.heckeT (N * r) H q 𝒪' v = ι (b q) • v) ∧
      (∀ d : (ZMod (N * r))ˣ, CohCarrier.diamondL (N * r) H 𝒪' d v = v) :=
  CohCarrier.O3Prim.main N r H g' hg' A ι hι b S hT hU

end S_CohCarrier_exists_primitive_mem_parabolicHoms_heckeT_eq_smul_level_mul_of_heckeTLin_eq_smul_of_notMem
end P2MW
export P2MW.S_CohCarrier_exists_primitive_mem_parabolicHoms_heckeT_eq_smul_level_mul_of_heckeTLin_eq_smul_of_notMem (solution)
