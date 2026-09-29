-- Prove2me | solution 1 for CohCarrier.exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4dbe5c2e-68a6-525e-8e70-5ed02ebbc344

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_PeriodHomPair
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_gammaH
import Theorems.Thm_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
import Theorems.Thm_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups ComplexConjugate

noncomputable section

namespace ParAsm

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} {p : ℕ}

theorem sl_slash (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

theorem slash_mem (g : CuspForm (CohCarrier.GammaH M H) k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M H) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

theorem mem_GammaH_of_mem_Gamma0_of_apply_11 {γ : SL(2, ℤ)} (h0 : γ ∈ Gamma0 M)
    (h1 : ((γ 1 1 : ℤ) : ZMod M) = 1) : γ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨γ, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h1
  rw [this]
  exact one_mem H

theorem Gamma1_le_GammaH : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro γ hγ
  have h0 : γ ∈ Gamma0 M := Gamma1_in_Gamma0 M hγ
  rw [Gamma1_mem] at hγ
  exact mem_GammaH_of_mem_Gamma0_of_apply_11 h0 (by simpa using hγ.2.1)

theorem T_mem_Gamma1' : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  Gamma1_le_GammaH T_mem_Gamma1'

theorem T_pow_mem_GammaH (n : ℕ) : ModularGroup.T ^ n ∈ CohCarrier.GammaH M H :=
  pow_mem T_mem_GammaH n

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem heckeDiagMatrix_mul_T (hp : p ≠ 0) :
    heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p) * heckeDiagMatrix p := by
  have hTp : ((ModularGroup.T ^ p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (p : ℤ); 0, 1] := by
    rw [show ModularGroup.T ^ p = ModularGroup.T ^ (p : ℤ) from (zpow_natCast _ p).symm]
    exact ModularGroup.coe_T_zpow (p : ℤ)
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, mapGL_apply, mapGL_apply, mapGL_apply, mapGL_apply, hTp, ModularGroup.coe_T,
    val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;> simp

theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  have hT : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ := by
    intro τ
    have := congrFun h τ
    change (F ∣[k] ModularGroup.T) τ = F τ at this
    rw [SL_slash_apply] at this
    rw [← modular_T_smul]
    rw [← this]
    simp [denom, ModularGroup.T]
  intro w
  by_cases hw : 0 < w.im
  · have : 0 < (w + 1).im := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw : w.im ≤ 0 := le_of_not_gt hw
    have : (w + 1).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

theorem slash_heckeDiagMatrix_slash_T (hp : p ≠ 0) {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p)) = F) :
    (F ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = F ∣[k] heckeDiagMatrix p := by
  rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_T hp, SlashAction.slash_mul, h]

theorem isBoundedAtImInfty_slash_heckeDiagMatrix (hp : p ≠ 0) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeDiagMatrix p) :=
  hF.slash k (by simp [val_heckeDiagMatrix hp])

theorem σ_heckeDiagMatrix_apply (p : ℕ) (c : ℂ) : UpperHalfPlane.σ (heckeDiagMatrix p) c = c := by
  rw [σ_heckeDiagMatrix]; rfl

structure Reg (F : ℍ → ℂ) : Prop where
  per : Periodic (F ∘ ofComplex) 1
  hol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F
  bdd : IsBoundedAtImInfty F

theorem reg_coe (g : CuspForm (CohCarrier.GammaH M H) k) : Reg (⇑g : ℍ → ℂ) :=
  ⟨periodic_of_slash_T (slash_mem g T_mem_GammaH), CuspFormClass.holo g,
    ModularFormClass.bdd_at_infty g⟩

theorem Reg.smul {F : ℍ → ℂ} (h : Reg F) (c : ℂ) : Reg (c • F) := by
  refine ⟨?_, h.hol.const_smul c, h.bdd.smul c⟩
  intro w
  have := h.per w
  simp only [comp_apply, Pi.smul_apply] at this ⊢
  rw [this]

theorem Reg.sub {F G : ℍ → ℂ} (hF : Reg F) (hG : Reg G) : Reg (F - G) := by
  refine ⟨?_, hF.hol.sub hG.hol, hF.bdd.sub hG.bdd⟩
  intro w
  have h1 := hF.per w
  have h2 := hG.per w
  simp only [comp_apply, Pi.sub_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem Reg.analyticAt {F : ℍ → ℂ} (h : Reg F) : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
  analyticAt_cuspFunction_zero one_pos h.per h.hol h.bdd

theorem reg_slash_heckeDiagMatrix (hp : p ≠ 0) (g : CuspForm (CohCarrier.GammaH M H) k) :
    Reg ((⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :=
  ⟨periodic_of_slash_T (slash_heckeDiagMatrix_slash_T hp (slash_mem g (T_pow_mem_GammaH p))),
    (CuspFormClass.holo g).slash k _, isBoundedAtImInfty_slash_heckeDiagMatrix hp
      (ModularFormClass.bdd_at_infty g)⟩

theorem qCoeff_const_smul {F : ℍ → ℂ} (h : Reg F) (c : ℂ) (n : ℕ) :
    ModularFormClass.qCoeff (c • F) n = c * ModularFormClass.qCoeff F n := by
  simp only [ModularFormClass.qCoeff]
  rw [qExpansion_smul h.analyticAt, map_smul, smul_eq_mul]

theorem qCoeff_sub {F G : ℍ → ℂ} (hF : Reg F) (hG : Reg G) (n : ℕ) :
    ModularFormClass.qCoeff (F - G) n = ModularFormClass.qCoeff F n - ModularFormClass.qCoeff G n := by
  have e : F - G = F + ((-1 : ℂ) • G) := by ext τ; simp [sub_eq_add_neg]
  have h1 : ModularFormClass.qCoeff (F + ((-1 : ℂ) • G)) n =
      ModularFormClass.qCoeff F n + ModularFormClass.qCoeff ((-1 : ℂ) • G) n := by
    simp only [ModularFormClass.qCoeff]
    rw [qExpansion_add hF.analyticAt (hG.smul _).analyticAt, map_add]
  rw [e, h1, qCoeff_const_smul hG, neg_one_mul, sub_eq_add_neg]

theorem qCoeff_of_coe_eq_heckeU_add_slash (hp : p ≠ 0)
    (F G : CuspForm (CohCarrier.GammaH M H) k) (ρ : Gamma0 M) (c : ℂ)
    (hρ : (⇑F : ℍ → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) = c • ⇑F)
    (hG : (⇑G : ℍ → ℂ) = heckeU k p ⇑F +
      ((⇑F : ℍ → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        heckeDiagMatrix p)))
    (n : ℕ) :
    ModularFormClass.qCoeff (⇑G) n =
      ModularFormClass.qCoeff (⇑F) (p * n) +
        c * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff (⇑F) (n / p) else 0) := by
  have hF := reg_coe F
  have hGr := reg_coe G

  set D : ℍ → ℂ := (⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hDdef
  have hD : Reg D := reg_slash_heckeDiagMatrix hp F
  have htw : (⇑F : ℍ → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      heckeDiagMatrix p) = c • D := by
    rw [SlashAction.slash_mul, hρ, ModularForm.smul_slash, σ_heckeDiagMatrix_apply]

  have hU : heckeU k p ⇑F = ⇑G - c • D := by rw [hG, htw, add_sub_cancel_right]
  have hUr : Reg (heckeU k p ⇑F) := by rw [hU]; exact hGr.sub (hD.smul c)

  have hqU : ModularFormClass.qCoeff (heckeU k p ⇑F) n = ModularFormClass.qCoeff (⇑F) (p * n) := by
    rw [UpperHalfPlane.qCoeff_heckeU hF.per hF.hol hF.bdd k hp n, coeffHeckeU_apply, mul_comm]
  have hqD : ModularFormClass.qCoeff D n
      = (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff (⇑F) (n / p) else 0) := by
    have hDG : D = ((p : ℂ) ^ (k - 1)) • (fun τ => F (heckeDiagMatrix p • τ)) := by
      funext τ
      rw [hDdef, slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
    have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
    have hGreg : Reg (fun τ => F (heckeDiagMatrix p • τ)) := by
      have : (fun τ => F (heckeDiagMatrix p • τ)) = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
        rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
      rw [this]; exact hD.smul _
    rw [hDG, qCoeff_const_smul hGreg]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hF.per hF.hol hF.bdd hp n
  have hG' : (⇑G : ℍ → ℂ) = heckeU k p ⇑F + c • D := by rw [hG, htw]
  calc ModularFormClass.qCoeff (⇑G) n
      = ModularFormClass.qCoeff (heckeU k p ⇑F + c • D) n := by rw [hG']
    _ = ModularFormClass.qCoeff (heckeU k p ⇑F) n + ModularFormClass.qCoeff (c • D) n := by
        simp only [ModularFormClass.qCoeff]
        rw [qExpansion_add hUr.analyticAt (hD.smul c).analyticAt, map_add]
    _ = _ := by rw [hqU, qCoeff_const_smul hD, hqD, mul_assoc]

def toGamma1 (F : CuspForm (CohCarrier.GammaH M H) k) : CuspForm (Gamma1 M) k where
  toFun := ⇑F
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    exact slash_mem F (Gamma1_le_GammaH hγ)
  holo' := CuspFormClass.holo F
  zero_at_cusps' := by
    intro c hc
    have hc' : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc
    exact CuspFormClass.zero_at_cusps F hc'

@[scoped simp] theorem coe_toGamma1 (F : CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(toGamma1 F) : ℍ → ℂ) = ⇑F := rfl

theorem hasNebentypus_toGamma1 (F : CuspForm (CohCarrier.GammaH M H) k) (ε : DirichletCharacter ℂ M)
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
        ε (((γ 1 1 : ℤ) : ZMod M)) • ⇑F) :
    CuspForm.HasNebentypus ε (toGamma1 F) := by
  intro γ hγ τ
  have hslash := congrFun (hF γ hγ) τ
  rw [← sl_slash, SL_slash_apply, Pi.smul_apply, smul_eq_mul] at hslash
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  rw [hden] at hslash
  have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ τ
  have hzk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hne
  have key : F (γ • τ) =
      ε (((γ 1 1 : ℤ) : ZMod M)) * F τ * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hzk]
    exact hslash
  change F (γ • τ) = ε ((γ 1 1 : ℤ) : ZMod M) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * F τ)
  rw [key, ← zpow_neg, neg_neg]
  ring

theorem exists_gamma1_coe_eq_and_hasNebentypus
    (F : CuspForm (CohCarrier.GammaH M H) k) (e : (ZMod M)ˣ →* ℂˣ)
    (hF : ∀ σ : Gamma0 M,
      (⇑F : ℍ → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ((e (CohCarrier.gamma0Units M σ) : ℂˣ) : ℂ) • ⇑F) :
    ∃ (ε : DirichletCharacter ℂ M) (F₁ : CuspForm (Gamma1 M) k),
      (⇑F₁ : ℍ → ℂ) = ⇑F ∧ CuspForm.HasNebentypus ε F₁ ∧
      ∀ u : (ZMod M)ˣ, ε (u : ZMod M) = ((e u : ℂˣ) : ℂ) := by
  refine ⟨MulChar.ofUnitHom e, toGamma1 F, rfl, ?_, fun u => ?_⟩
  · apply hasNebentypus_toGamma1
    intro γ hγ
    have h := hF ⟨γ, hγ⟩
    have hu : (((γ 1 1 : ℤ) : ZMod M)) = ((CohCarrier.gamma0Units M ⟨γ, hγ⟩ : (ZMod M)ˣ) : ZMod M) := by
      rw [CohCarrier.val_gamma0Units]; rfl
    rw [hu, MulChar.ofUnitHom_coe]
    exact h
  · exact MulChar.ofUnitHom_coe e u

end ParAsm
p2m_reactivate "P2MW.S_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul.ParAsm"

open ParAsm in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) (hφ0 : φ ≠ 0)
    (a : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ (ε : DirichletCharacter ℂ M) (h : CuspForm (CongruenceSubgroup.Gamma1 M) 2),
      CuspForm.IsEigenformWith ε h ∧
      (∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → ModularFormClass.qCoeff h ℓ = a ℓ) := by
  classical

  obtain ⟨J, ES, -, -, hinj, hrange, hTℓ, -, hDd⟩ := CohCarrier.exists_eichlerShimura_H1_gammaH M H
  have hφ : φ ∈ LinearMap.range ES := hrange ▸ hφpar
  obtain ⟨fg, rfl⟩ := hφ
  obtain ⟨f, g⟩ := fg

  have hTfg : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (hℓM : ¬ ℓ ∣ M),
      CuspForm.heckeTLinH 2 hℓ hℓM f = a ℓ • f ∧ CuspForm.heckeTLinH 2 hℓ hℓM g = a ℓ • g := by
    intro ℓ hℓ hℓS hℓM
    have h1 := hTℓ ℓ hℓ hℓM f g
    have h2 := hT ℓ hℓ hℓS hℓM
    have h3 : ES (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) = ES (a ℓ • (f, g)) := by
      rw [map_smul]; exact h1.trans h2
    have h4 := hinj h3
    rw [Prod.smul_mk, Prod.mk.injEq] at h4
    exact h4
  have hDfg : ∀ u : (ZMod M)ˣ,
      CuspForm.diamondLinH 2 u f = ((e u : ℂˣ) : ℂ) • f ∧ CuspForm.diamondLinH 2 u g = ((e u : ℂˣ) : ℂ) • g := by
    intro u
    have h3 : ES (CuspForm.diamondLinH 2 u f, CuspForm.diamondLinH 2 u g) = ES (((e u : ℂˣ) : ℂ) • (f, g)) := by
      rw [map_smul]; exact (hDd u f g).trans (hD u)
    have h4 := hinj h3
    rw [Prod.smul_mk, Prod.mk.injEq] at h4
    exact h4

  have hfg : ((f, g) : CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2) ≠ 0 := by
    intro h0; exact hφ0 (by rw [h0, map_zero])
  obtain ⟨F, hF0, hTF, hDF⟩ : ∃ F : CuspForm (CohCarrier.GammaH M H) 2, F ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (hℓM : ¬ ℓ ∣ M), CuspForm.heckeTLinH 2 hℓ hℓM F = a ℓ • F) ∧
      (∀ u : (ZMod M)ˣ, CuspForm.diamondLinH 2 u F = ((e u : ℂˣ) : ℂ) • F) := by
    by_cases hf : f = 0
    · refine ⟨g, ?_, fun ℓ hℓ hS hM => (hTfg ℓ hℓ hS hM).2, fun u => (hDfg u).2⟩
      intro hg; apply hfg; rw [hf, hg]; rfl
    · exact ⟨f, hf, fun ℓ hℓ hS hM => (hTfg ℓ hℓ hS hM).1, fun u => (hDfg u).1⟩

  have hSD : CuspForm.StableD M H 2 := CuspForm.stableD M H 2
  have hslash : ∀ σ : Gamma0 M,
      (⇑F : ℍ → ℂ) ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ((e (CohCarrier.gamma0Units M σ) : ℂˣ) : ℂ) • ⇑F := by
    intro σ
    rw [← CuspForm.coe_diamondLinH_eq_slash 2 hSD (CohCarrier.gamma0Units M σ) σ rfl F,
      hDF (CohCarrier.gamma0Units M σ), CuspForm.IsGLPos.coe_smul]

  obtain ⟨ε, F₁, hF₁F, hεF₁, hεe⟩ := ParAsm.exists_gamma1_coe_eq_and_hasNebentypus F e hslash
  have hF₁0 : F₁ ≠ 0 := by
    intro h0; apply hF0
    apply DFunLike.coe_injective
    have h1 : (⇑F₁ : ℍ → ℂ) = ⇑(0 : CuspForm (Gamma1 M) 2) := by rw [h0]
    rw [CuspForm.coe_zero, hF₁F] at h1
    show (⇑F : ℍ → ℂ) = ⇑(0 : CuspForm (CohCarrier.GammaH M H) 2)
    rw [h1, CuspForm.coe_zero]

  have hcoef : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff F₁ (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ ((2 : ℤ) - 1) *
            (if p ∣ n then ModularFormClass.qCoeff F₁ (n / p) else 0) =
        a p * ModularFormClass.qCoeff F₁ n := by
    intro p hp hpS hpM n
    have hp0 : p ≠ 0 := hp.ne_zero
    have hST : CuspForm.StableT M H 2 p := CuspForm.stableT M H 2 hp hpM
    set ρ : Gamma0 M := CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hp hpM) with hρdef

    have hunit : CohCarrier.gamma0Units M ρ = CuspForm.unitOfPrimeNotDvd hp hpM :=
      CuspForm.gamma0Units_gammaLift _
    have hcoeU : ((CuspForm.unitOfPrimeNotDvd (M := M) hp hpM : (ZMod M)ˣ) : ZMod M) = (p : ZMod M) := by
      simp [CuspForm.unitOfPrimeNotDvd]
    have hc : ((e (CohCarrier.gamma0Units M ρ) : ℂˣ) : ℂ) = ε (p : ZMod M) := by
      rw [hunit, ← hcoeU, hεe]

    set G := CuspForm.heckeTLinH 2 hp hpM F with hGdef
    have eG : (⇑G : ℍ → ℂ) = heckeU 2 p ⇑F +
        ((⇑F : ℍ → ℂ) ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          heckeDiagMatrix p)) := CuspForm.coe_heckeTLinH_apply 2 hp hpM hST F
    have eG' : (⇑G : ℍ → ℂ) = a p • ⇑F := by
      rw [hGdef, hTF p hp hpS hpM, CuspForm.IsGLPos.coe_smul]
    have h1 : ModularFormClass.qCoeff (⇑G) n =
        ModularFormClass.qCoeff (⇑F) (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ ((2 : ℤ) - 1) *
            (if p ∣ n then ModularFormClass.qCoeff (⇑F) (n / p) else 0) := by
      have := qCoeff_of_coe_eq_heckeU_add_slash hp0 F G ρ _ (hslash ρ) eG n
      rwa [hc] at this
    have h2 : ModularFormClass.qCoeff (⇑G) n = a p * ModularFormClass.qCoeff (⇑F) n := by
      rw [eG', qCoeff_const_smul (reg_coe F)]
    rw [hF₁F, ← h1, h2]

  obtain ⟨g₀, b, hg0, hεg, hba, hTall, hUall⟩ :=
    CuspForm.exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
      M 2 ε S F₁ hF₁0 hεF₁ a hcoef
  obtain ⟨-, hEig, hbp⟩ :=
    CuspForm.qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
      M 2 ε g₀ hg0 hεg b hTall hUall
  exact ⟨ε, (ModularFormClass.qCoeff g₀ 1)⁻¹ • g₀, hEig, hεe,
    fun ℓ hℓ hℓS hℓM => by rw [CuspForm.IsGLPos.coe_smul, hbp ℓ hℓ, hba ℓ hℓ hℓS hℓM]⟩

end
p2m_reactivate "P2MW.S_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul.ParAsm"

end S_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
end P2MW
export P2MW.S_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul (solution)
