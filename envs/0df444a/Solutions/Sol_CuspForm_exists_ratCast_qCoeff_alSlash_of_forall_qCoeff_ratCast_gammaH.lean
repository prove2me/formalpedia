-- Prove2me | solution 1 for CuspForm.exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c61762fa-b0e2-504a-89b0-898f9193536d

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_CuspForm_span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top
import Theorems.Thm_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
import Theorems.Thm_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem
import Theorems.Thm_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one"
p2m_attr_erase "simp" "Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise Manifold
open CongruenceSubgroup CohCarrier UpperHalfPlane

namespace AtkinLiRat

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_GammaH : ModularGroup.T ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_GammaH]
  exact AddSubgroup.mem_zmultiples _

theorem isCusp_infty : IsCusp OnePoint.infty (Γ M H) :=
  Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods

theorem mem_GammaH_of_unitsMap_eq {R : ℕ} (hR : R ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap hR u = 1 → u ∈ H)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (h : ZMod.unitsMap hR (gamma0Units M ⟨δ, hδ⟩) = ZMod.unitsMap hR u) :
    δ ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  refine ⟨hδ, ?_⟩
  have hker : gamma0Units M ⟨δ, hδ⟩ * u⁻¹ ∈ H :=
    hHp _ (by rw [map_mul, map_inv, h, mul_inv_cancel])
  simpa using H.mul_mem hker hu

theorem hHp_transfer {R₁ R₂ : ℕ} (h₁ : R₁ ∣ M) (h₂ : R₂ ∣ M) (heq : R₁ = R₂)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap h₁ u = 1 → u ∈ H) :
    ∀ u : (ZMod M)ˣ, ZMod.unitsMap h₂ u = 1 → u ∈ H := by
  subst heq
  exact hHp

theorem Gamma0_le_of_dvd {R : ℕ} (hR : R ∣ M) : Gamma0 M ≤ Gamma0 R := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have := congrArg (ZMod.castHom hR (ZMod R)) hγ
  rw [map_zero, map_intCast] at this
  exact this

theorem unitsMap_gamma0Units {R : ℕ} [NeZero R] (hR : R ∣ M) (σ : Gamma0 M) :
    ZMod.unitsMap hR (gamma0Units M σ) = gamma0Units R ⟨σ, Gamma0_le_of_dvd hR σ.2⟩ := by
  ext
  rw [ZMod.unitsMap_val, val_gamma0Units, val_gamma0Units]
  show ((((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M).cast : ZMod R) = (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod R)
  rw [ZMod.cast_intCast hR]

theorem Gamma1_le_GammaH : Gamma1 M ≤ GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨_, h11, h10⟩ := hA
  rw [mem_GammaH_iff]
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact h10
  refine ⟨h0, ?_⟩
  have : gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    exact h11
  rw [this]
  exact one_mem H

end Group

section Forms

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ}

scoped instance instFiniteDimensional [NeZero M] : FiniteDimensional ℂ (CuspForm (Γ M H) k) :=
  CuspForm.finiteDimensional_of_isArithmetic (Γ M H) k

def restrictCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) : CuspForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono h)

@[scoped simp] theorem coe_restrictCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) :
    ⇑(restrictCusp h f) = ⇑f := rfl

def slashCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : CuspForm Γ₁ k) : CuspForm Γ₂ k :=
  restrictCusp hg (CuspForm.translate f g)

@[scoped simp] theorem coe_slashCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : CuspForm Γ₁ k) :
    ⇑(slashCusp g hg f) = ⇑f ∣[k] g := rfl

def coef (n : ℕ) : CuspForm (Γ M H) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := by
    show PowerSeries.coeff n (qExpansion 1 ⇑(f + g)) =
      PowerSeries.coeff n (qExpansion 1 ⇑f) + PowerSeries.coeff n (qExpansion 1 ⇑g)
    rw [CuspForm.coe_add, qExpansion_add
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods)
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods), map_add]
  map_smul' c f := by
    show PowerSeries.coeff n (qExpansion 1 ⇑(c • f)) = c • PowerSeries.coeff n (qExpansion 1 ⇑f)
    rw [CuspForm.IsGLPos.coe_smul, qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods), map_smul]

theorem coef_apply (n : ℕ) (f : CuspForm (Γ M H) k) : coef n f = ModularFormClass.qCoeff (⇑f) n := rfl

theorem eq_zero_of_forall_coef_eq_zero (f : CuspForm (Γ M H) k) (h : ∀ n, coef n f = 0) : f = 0 := by
  have hq : qExpansion 1 (⇑f) = 0 := by
    ext n
    rw [map_zero]
    exact h n
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods
  haveI : Fact (IsCusp OnePoint.infty (Γ M H)) := ⟨isCusp_infty⟩
  have hzero := (qExpansion_eq_zero_iff one_pos hper (CuspFormClass.holo f)
    (ModularFormClass.bdd_at_infty f)).mp hq
  exact DFunLike.coe_injective (hzero.trans CuspForm.coe_zero.symm)

theorem coef_of_coe_eq_slash_heckeDiagMatrix {Θ Φ : CuspForm (Γ M H) k} {d : ℕ} (hd : d ≠ 0)
    (h : ⇑Θ = ⇑Φ ∣[k] ModularForm.heckeDiagMatrix d) (n : ℕ) :
    coef n Θ = (d : ℂ) ^ (k - 1) * (if d ∣ n then coef (n / d) Φ else 0) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hpow : (d : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ hdC
  have hfun : (fun τ : ℍ => Φ (ModularForm.heckeDiagMatrix d • τ)) = ⇑(((d : ℂ) ^ (k - 1))⁻¹ • Θ) := by
    funext τ
    rw [CuspForm.IsGLPos.smul_apply, h, ModularForm.slash_heckeDiagMatrix_apply k hd, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
  have key := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul Φ one_mem_strictPeriods hd n
  rw [hfun, ← coef_apply, map_smul, smul_eq_mul] at key
  have e : coef n Θ = (d : ℂ) ^ (k - 1) * (((d : ℂ) ^ (k - 1))⁻¹ * coef n Θ) := by
    rw [← mul_assoc, mul_inv_cancel₀ hpow, one_mul]
  rw [e, key]
  rfl

theorem coef_heckeULinH [NeZero M] {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : CuspForm (Γ M H) k) (n : ℕ) :
    coef n (CuspForm.heckeULinH k q f) = coef (n * q) f := by
  rw [coef_apply, coef_apply, CuspForm.coe_heckeULinH_apply k (CuspForm.stableU M H k hq hqM) f,
    ModularFormClass.qCoeff_heckeU f one_mem_strictPeriods hq.ne_zero n, ModularForm.coeffHeckeU_apply]

def IsRat (f : CuspForm (Γ M H) k) : Prop := ∀ n : ℕ, ∃ r : ℚ, coef n f = (r : ℂ)

theorem IsRat.zero : IsRat (0 : CuspForm (Γ M H) k) := fun n => ⟨0, by simp⟩

theorem IsRat.add {f g : CuspForm (Γ M H) k} (hf : IsRat f) (hg : IsRat g) : IsRat (f + g) := fun n => by
  obtain ⟨r, hr⟩ := hf n
  obtain ⟨s, hs⟩ := hg n
  exact ⟨r + s, by rw [map_add, hr, hs, Rat.cast_add]⟩

theorem IsRat.sub {f g : CuspForm (Γ M H) k} (hf : IsRat f) (hg : IsRat g) : IsRat (f - g) := fun n => by
  obtain ⟨r, hr⟩ := hf n
  obtain ⟨s, hs⟩ := hg n
  exact ⟨r - s, by rw [map_sub, hr, hs, Rat.cast_sub]⟩

theorem IsRat.ratSmul {f : CuspForm (Γ M H) k} (hf : IsRat f) (q : ℚ) : IsRat (((q : ℚ) : ℂ) • f) := fun n => by
  obtain ⟨r, hr⟩ := hf n
  exact ⟨q * r, by rw [map_smul, hr, smul_eq_mul, Rat.cast_mul]⟩

theorem IsRat.sum {ι : Type*} (s : Finset ι) {f : ι → CuspForm (Γ M H) k} (hf : ∀ i ∈ s, IsRat (f i)) :
    IsRat (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact IsRat.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem IsRat.of_intCast {f : CuspForm (Γ M H) k} (hf : ∀ n : ℕ, ∃ a : ℤ, coef n f = (a : ℂ)) : IsRat f :=
  fun n => by obtain ⟨a, ha⟩ := hf n; exact ⟨a, by rw [ha, Rat.cast_intCast]⟩

theorem IsRat.heckeULinH [NeZero M] {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) {f : CuspForm (Γ M H) k}
    (hf : IsRat f) : IsRat (CuspForm.heckeULinH k q f) := fun n => by
  obtain ⟨r, hr⟩ := hf (n * q)
  exact ⟨r, by rw [coef_heckeULinH hq hqM, hr]⟩

def coeL : CuspForm (Γ M H) k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ⇑f
  map_add' f g := CuspForm.coe_add f g
  map_smul' c f := FunLike.coe_smul c f

theorem coeL_injective : Function.Injective (coeL : CuspForm (Γ M H) k →ₗ[ℂ] (ℍ → ℂ)) :=
  fun _ _ h => DFunLike.coe_injective h

theorem exists_rat_coord {ι : Type*} [Fintype ι] (w : ι → CuspForm (Γ M H) k) (hw : LinearIndependent ℂ w)
    (hwrat : ∀ i, IsRat (w i)) (r : CuspForm (Γ M H) k) (hr : IsRat r)
    (hmem : r ∈ Submodule.span ℂ (Set.range w)) :
    ∃ q : ι → ℚ, r = ∑ i, ((q i : ℚ) : ℂ) • w i := by
  classical
  set K : IntermediateField ℚ ℂ := ⊥ with hK

  let F : Option ι → ℍ → ℂ := fun o => o.elim (⇑r) fun i => ⇑(w i)
  have hFsome : (F ∘ ((↑) : ι → Option ι)) = fun i => ⇑(w i) := rfl
  have hFnone : F none = ⇑r := rfl

  have hyp : ∀ o, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F o) ∧ ∃ m : ℕ,
      Function.Periodic ((F o * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) (1 : ℕ) ∧
      UpperHalfPlane.IsBoundedAtImInfty (F o * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℕ) (F o * ModularForm.discriminant ^ m)).coeff n ∈ K := by
    have key : ∀ g : CuspForm (Γ M H) k, IsRat g → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑g) ∧ ∃ m : ℕ,
        Function.Periodic ((⇑g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) (1 : ℕ) ∧
        UpperHalfPlane.IsBoundedAtImInfty (⇑g * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℕ) (⇑g * ModularForm.discriminant ^ m)).coeff n ∈ K := by
      intro g hg
      haveI : Fact (IsCusp OnePoint.infty (Γ M H)) := ⟨isCusp_infty⟩
      refine ⟨g.holo', 0, ?_, ?_, ?_⟩
      · rw [pow_zero, mul_one, Nat.cast_one]
        have := SlashInvariantFormClass.periodic_comp_ofComplex g one_mem_strictPeriods
        simpa using this
      · rw [pow_zero, mul_one]
        exact ModularFormClass.bdd_at_infty g
      · intro n
        rw [pow_zero, mul_one, Nat.cast_one]
        obtain ⟨q, hq⟩ := hg n
        rw [coef_apply] at hq
        change (qExpansion 1 ⇑g).coeff n = (q : ℂ) at hq
        rw [hq, hK, IntermediateField.mem_bot]
        exact ⟨q, rfl⟩
    intro o
    cases o with
    | none => exact key r hr
    | some i => exact key (w i) (hwrat i)

  have hdep : ¬ LinearIndependent ℂ F := by
    intro hli
    have h2 := (linearIndependent_option.mp hli).2
    apply h2
    rw [hFnone, hFsome]
    have : (⇑r : ℍ → ℂ) = coeL r := rfl
    rw [this]
    have hmap := Submodule.mem_map_of_mem (f := (coeL : CuspForm (Γ M H) k →ₗ[ℂ] (ℍ → ℂ))) hmem
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    exact hmap

  have hdepK : ¬ LinearIndependent K F := fun hli =>
    hdep (UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem 1 K F hyp hli)

  have hwK : LinearIndependent K (F ∘ ((↑) : ι → Option ι)) := by
    rw [hFsome]
    have hC : LinearIndependent ℂ (fun i => (⇑(w i) : ℍ → ℂ)) := by
      have := hw.map' (coeL : CuspForm (Γ M H) k →ₗ[ℂ] (ℍ → ℂ))
        (LinearMap.ker_eq_bot.mpr coeL_injective)
      exact this
    exact hC.restrict_scalars' K
  have hspan : F none ∈ Submodule.span K (Set.range (F ∘ ((↑) : ι → Option ι))) := by
    by_contra hnot
    exact hdepK (linearIndependent_option.mpr ⟨hwK, hnot⟩)
  rw [hFsome, hFnone] at hspan
  obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  have hq : ∀ i, ∃ q : ℚ, ((κ i : K) : ℂ) = (q : ℂ) := fun i => by
    have hmem : ((κ i : K) : ℂ) ∈ (⊥ : IntermediateField ℚ ℂ) := (κ i).2
    rw [IntermediateField.mem_bot] at hmem
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq.symm⟩
  choose q hq using hq
  refine ⟨q, ?_⟩
  apply DFunLike.coe_injective
  show (⇑r : ℍ → ℂ) = coeL (∑ i, ((q i : ℚ) : ℂ) • w i)
  rw [map_sum, ← hκ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← hq i]
  rfl

theorem IsRat.of_eq_sum_ratSmul {ι : Type*} [Fintype ι] {w : ι → CuspForm (Γ M H) k} (hwrat : ∀ i, IsRat (w i))
    {r : CuspForm (Γ M H) k} (q : ι → ℚ) (h : r = ∑ i, ((q i : ℚ) : ℂ) • w i) : IsRat r := by
  rw [h]
  exact IsRat.sum _ fun i _ => (hwrat i).ratSmul (q i)

open Module Submodule in

theorem exists_basis_mem {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {s : Set W} (hs : span ℂ s = ⊤) :
    ∃ v : Basis (Fin (finrank ℂ W)) ℂ W, ∀ i, v i ∈ s := by
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℂ s
  rw [hs] at hspan
  have hfin : b.Finite := hli.setFinite
  letI : Fintype b := hfin.fintype
  let B : Basis b ℂ W := Basis.mk hli (by rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan])
  have hcard : Fintype.card b = finrank ℂ W := (Module.finrank_eq_card_basis B).symm
  refine ⟨B.reindex (Fintype.equivFinOfCardEq hcard), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hbs (Subtype.coe_prop _)

theorem exists_basis_heckeIntegral (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ v : Module.Basis (Fin (Module.finrank ℂ (CuspForm (Γ M H) 2))) ℂ (CuspForm (Γ M H) 2),
      ∀ i, ∀ t ∈ CuspForm.heckeRingH M H 2, ∀ n : ℕ, ∃ a : ℤ, coef n (t (v i)) = (a : ℂ) := by
  obtain ⟨v, hv⟩ := exists_basis_mem (W := CuspForm (Γ M H) 2)
    (CuspForm.span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top M H)
  exact ⟨v, fun i => hv i⟩

theorem isRat_of_mem_heckeRingH [NeZero M] {t : CuspForm (Γ M H) 2 →ₗ[ℂ] CuspForm (Γ M H) 2}
    (ht : t ∈ CuspForm.heckeRingH M H 2) {f : CuspForm (Γ M H) 2} (hf : IsRat f) : IsRat (t f) := by
  obtain ⟨v, hv⟩ := exists_basis_heckeIntegral M H
  have hvrat : ∀ i, IsRat (v i) := fun i => IsRat.of_intCast fun n => by
    obtain ⟨a, ha⟩ := hv i 1 (Subring.one_mem _) n
    exact ⟨a, by simpa using ha⟩
  obtain ⟨q, hq⟩ := exists_rat_coord v v.linearIndependent hvrat f hf (by rw [v.span_eq]; trivial)
  have htv : ∀ i, IsRat (t (v i)) := fun i => IsRat.of_intCast (hv i t ht)
  refine IsRat.of_eq_sum_ratSmul htv q ?_
  rw [hq, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]

theorem diamondLinH_diamondLinH [NeZero M] (d e : (ZMod M)ˣ) (f : CuspForm (Γ M H) k) :
    CuspForm.diamondLinH k d (CuspForm.diamondLinH k e f) = CuspForm.diamondLinH k (d * e) f := by
  have hD := CuspForm.stableD M H k
  apply DFunLike.coe_injective
  rw [CuspForm.coe_diamondLinH_apply k hD d, CuspForm.coe_diamondLinH_apply k hD e, ← SlashAction.slash_mul,
    ← map_mul]
  have hσ : gamma0Units M (CuspForm.gammaLift M e * CuspForm.gammaLift M d) = d * e := by
    rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift, mul_comm]
  rw [CuspForm.coe_diamondLinH_eq_slash k hD (d * e) (CuspForm.gammaLift M e * CuspForm.gammaLift M d) hσ f]
  rfl

theorem diamondLinH_one [NeZero M] (f : CuspForm (Γ M H) k) : CuspForm.diamondLinH k 1 f = f := by
  apply DFunLike.coe_injective
  rw [CuspForm.coe_diamondLinH_eq_slash k (CuspForm.stableD M H k) 1 1 (map_one _) f]
  show ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑f
  rw [map_one, SlashAction.slash_one]

theorem diamondLinH_inv_apply [NeZero M] (d : (ZMod M)ˣ) (f : CuspForm (Γ M H) k) :
    CuspForm.diamondLinH k d⁻¹ (CuspForm.diamondLinH k d f) = f := by
  rw [diamondLinH_diamondLinH, inv_mul_cancel, diamondLinH_one]

end Forms

section AL

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} (W : ModularForm.AtkinLehnerDatum M p)

omit [NeZero M] in

theorem R_dvd : W.R ∣ M := Dvd.intro_left p W.hM.symm

scoped instance instNeZeroR : NeZero W.R := ⟨W.R_pos.ne'⟩

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem exists_alGL_mul_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
        = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) := by
  obtain ⟨δ, hδ, hW⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq W hγ
  refine ⟨δ, hδ, hW, ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast W.q_pos.ne'
  have h11 := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hW
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.alGL_coe,
    mapGL_coe_eq, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] at h11
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, eq_intCast] at h11
  have hZ : (p : ℤ) * (W.R : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (p : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * W.b + (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (p : ℤ) := by
    exact_mod_cast h11
  have hMδ : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hδ
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨s, hs⟩ := hMδ
  rw [hs, W.hM_int] at hZ
  have hcancel : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 + (W.R : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 - s * W.b) := by
    have : (p : ℤ) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
        - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 + (W.R : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 - s * W.b))) = 0 := by
      linear_combination -hZ
    have h2 := (mul_eq_zero.mp this).resolve_left hp0
    linear_combination h2
  rw [hcancel]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]

theorem le_conj_alGL (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H) :
    Γ M H ≤ ConjAct.toConjAct W.alGL⁻¹ • Γ M H := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  obtain ⟨δ, hδ, hW, hcong⟩ := exists_alGL_mul_eq W hγ0
  refine ⟨δ, ?_, ?_⟩
  · refine mem_GammaH_of_unitsMap_eq (R_dvd W) hHp hδ hγH ?_
    rw [unitsMap_gamma0Units, unitsMap_gamma0Units]
    ext
    rw [val_gamma0Units, val_gamma0Units]
    exact hcong
  · show (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ)
      = W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ * W.alGL⁻¹
    rw [hW, mul_inv_cancel_right]

def alLin (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H) (k : ℤ) :
    CuspForm (Γ M H) k →ₗ[ℂ] CuspForm (Γ M H) k where
  toFun f := slashCusp W.alGL (le_conj_alGL W hHp) f
  map_add' f g := DFunLike.coe_injective <| by
    show ⇑(f + g) ∣[k] W.alGL = ⇑f ∣[k] W.alGL + ⇑g ∣[k] W.alGL
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show ⇑(c • f) ∣[k] W.alGL = c • (⇑f ∣[k] W.alGL)
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.smul_slash, ModularForm.AtkinLehnerDatum.σ_alGL_apply]

@[scoped simp] theorem coe_alLin (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H) (k : ℤ)
    (f : CuspForm (Γ M H) k) : ⇑(alLin W hHp k f) = ModularForm.alSlash W k ⇑f := rfl

def scalarGL (hp : 0 < p) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(p : ℝ), 0; 0, (p : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa using mul_ne_zero hp' hp')

@[scoped simp] lemma scalarGL_coe (hp : 0 < p) :
    (scalarGL hp : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, (p : ℝ)] := rfl

lemma slash_scalarGL_two (hp : 0 < p) (f : ℍ → ℂ) : f ∣[(2 : ℤ)] scalarGL hp = f := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdet : ((scalarGL hp).det : ℝ) = (p : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_fin_two_of]; ring
  have hdetpos : 0 < ((scalarGL hp).det : ℝ) := by rw [hdet]; positivity
  have hsmul : ∀ τ : ℍ, scalarGL hp • τ = τ := by
    intro τ
    have hqC : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hdetpos]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, scalarGL_coe]
    field_simp
  ext τ
  rw [ModularForm.slash_apply]
  have hσ : σ (scalarGL hp) (f (scalarGL hp • τ)) = f (scalarGL hp • τ) := by
    rw [UpperHalfPlane.σ, if_pos hdetpos]; rfl
  rw [hσ, hsmul, hdet]
  have hden : denom (scalarGL hp) τ = (p : ℂ) := by
    simp [UpperHalfPlane.denom, scalarGL_coe]
  rw [hden, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)]
  have h1 : (((p : ℝ) ^ 2 : ℝ) : ℂ) = (p : ℂ) ^ (2 : ℕ) := by push_cast; ring
  rw [h1, ← zpow_natCast (p : ℂ) 2, ← zpow_mul, mul_assoc, ← zpow_add₀ hpC]
  norm_num

lemma map_int_mul_eq (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

lemma alGL_mul_alGL :
    W.alGL * W.alGL = scalarGL W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
      = (scalarGL W.q_pos : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [ModularForm.AtkinLehnerDatum.alGL_coe, scalarGL_coe, mapGL_coe_eq,
    ModularForm.AtkinLehnerDatum.sqUnitSL_coe, ← map_int_mul_eq, W.mat_sq]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.natCast_apply]

theorem alSlash_alSlash_two (f : ℍ → ℂ) :
    ModularForm.alSlash W 2 (ModularForm.alSlash W 2 f)
      = f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) := by
  rw [ModularForm.alSlash_def, ModularForm.alSlash_def, ← SlashAction.slash_mul, alGL_mul_alGL,
    SlashAction.slash_mul, slash_scalarGL_two]

def sqUnitU : (ZMod M)ˣ := gamma0Units M ⟨W.sqUnitSL, W.sqUnitSL_mem⟩

theorem alLin_alLin_two (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H)
    (f : CuspForm (Γ M H) 2) :
    alLin W hHp 2 (alLin W hHp 2 f) = CuspForm.diamondLinH 2 (sqUnitU W) f := by
  apply DFunLike.coe_injective
  rw [coe_alLin, coe_alLin, alSlash_alSlash_two,
    CuspForm.coe_diamondLinH_eq_slash 2 (CuspForm.stableD M H 2) (sqUnitU W) ⟨W.sqUnitSL, W.sqUnitSL_mem⟩ rfl f]

def gammaW : SL(2, ℤ) :=
  ⟨!![W.a, W.b; (W.R : ℤ), (p : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

omit [NeZero M] in
theorem gammaW_mem : gammaW W ∈ Gamma0 W.R := by
  rw [Gamma0_mem]
  show (((W.R : ℤ) : ℤ) : ZMod W.R) = 0
  push_cast
  exact ZMod.natCast_self _

omit [NeZero M] in
theorem gammaW_apply_11 : ((gammaW W : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = (p : ℤ) := rfl

theorem alGL_eq_gammaW_mul (hp : p ≠ 0) :
    W.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (gammaW W) * ModularForm.heckeDiagMatrix p := by
  apply Units.ext
  rw [Units.val_mul]
  show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) =
    ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaW W) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      (ModularForm.heckeDiagMatrix p : Matrix (Fin 2) (Fin 2) ℝ)
  rw [ModularForm.AtkinLehnerDatum.alGL_coe, mapGL_coe_eq, ModularForm.val_heckeDiagMatrix hp,
    ModularForm.AtkinLehnerDatum.mat, gammaW]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> ring

def pUnit : (ZMod W.R)ˣ where
  val := (p : ZMod W.R)
  inv := ((W.a : ℤ) : ZMod W.R)
  val_inv := by
    have := congrArg (Int.cast : ℤ → ZMod W.R) W.bezout
    push_cast at this
    rw [ZMod.natCast_self, zero_mul, sub_zero] at this
    exact this
  inv_val := by
    have := congrArg (Int.cast : ℤ → ZMod W.R) W.bezout
    push_cast at this
    rw [ZMod.natCast_self, zero_mul, sub_zero] at this
    rw [mul_comm]; exact this

omit [NeZero M] in
@[scoped simp] theorem val_pUnit : (pUnit W : ZMod W.R) = (p : ZMod W.R) := rfl

omit [NeZero M] in
theorem gamma0Units_gammaW : gamma0Units W.R ⟨gammaW W, gammaW_mem W⟩ = pUnit W := by
  ext
  rw [val_gamma0Units, val_pUnit]
  show ((((gammaW W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) = _
  rw [gammaW_apply_11]
  push_cast
  rfl

omit [NeZero M] in

theorem not_dvd_R (hp : p.Prime) : ¬ p ∣ W.R := by
  rintro ⟨c, hc⟩
  have h := W.bezout
  rw [hc] at h
  push_cast at h
  have : (p : ℤ) ∣ 1 := ⟨W.a - c * W.b, by linear_combination -h⟩
  exact hp.not_dvd_one (by exact_mod_cast this)

end AL

section LevelPair

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} (W : ModularForm.AtkinLehnerDatum M p) {k : ℤ}

def Hlow (H : Subgroup (ZMod M)ˣ) : Subgroup (ZMod W.R)ˣ := H.map (ZMod.unitsMap (R_dvd W))

theorem GammaH_le_GammaH_low : GammaH M H ≤ GammaH W.R (Hlow W H) := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  rw [mem_GammaH_iff]
  refine ⟨Gamma0_le_of_dvd (R_dvd W) hA0, ?_⟩
  have := unitsMap_gamma0Units (R_dvd W) ⟨A, hA0⟩
  rw [Hlow, Subgroup.mem_map]
  exact ⟨_, hAH, this⟩

theorem Γ_le_Γ_low : Γ M H ≤ Γ W.R (Hlow W H) := Subgroup.map_mono (GammaH_le_GammaH_low W)

private def _root_.AtkinLiRat.raise : CuspForm (Γ W.R (Hlow W H)) k →ₗ[ℂ] CuspForm (Γ M H) k where
  toFun h := restrictCusp (Γ_le_Γ_low W) h
  map_add' _ _ := DFunLike.coe_injective rfl
  map_smul' _ _ := DFunLike.coe_injective rfl

p2m_export "AtkinLiRat" "raise"
@[scoped simp] theorem coe_raise (h : CuspForm (Γ W.R (Hlow W H)) k) : ⇑(raise W h : CuspForm (Γ M H) k) = ⇑h := rfl

theorem coef_raise (n : ℕ) (h : CuspForm (Γ W.R (Hlow W H)) k) : coef n (raise W h : CuspForm (Γ M H) k) = coef n h :=
  rfl

theorem raise_injective : Function.Injective (raise W : CuspForm (Γ W.R (Hlow W H)) k →ₗ[ℂ] CuspForm (Γ M H) k) :=
  fun _ _ h => DFunLike.coe_injective (congrArg (fun g : CuspForm (Γ M H) k => ⇑g) h)

theorem IsRat.raise {h : CuspForm (Γ W.R (Hlow W H)) k} (hh : IsRat h) : IsRat (raise W h : CuspForm (Γ M H) k) :=
  hh

def lower (φ : CuspForm (Γ M H) k) (hφ : ∀ γ ∈ Γ W.R (Hlow W H), ⇑φ ∣[k] γ = ⇑φ) :
    CuspForm (Γ W.R (Hlow W H)) k where
  toFun := φ
  slash_action_eq' A hA := hφ A hA
  holo' := φ.holo'
  zero_at_cusps' hc := by
    exact CuspFormClass.zero_at_cusps φ
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ M H)).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ W.R (Hlow W H))).mp hc))

@[scoped simp] theorem coe_lower (φ : CuspForm (Γ M H) k) (hφ : ∀ γ ∈ Γ W.R (Hlow W H), ⇑φ ∣[k] γ = ⇑φ) :
    ⇑(lower W φ hφ) = ⇑φ := rfl

theorem raise_lower (φ : CuspForm (Γ M H) k) (hφ : ∀ γ ∈ Γ W.R (Hlow W H), ⇑φ ∣[k] γ = ⇑φ) :
    raise W (lower W φ hφ) = φ :=
  DFunLike.coe_injective rfl

theorem levelLE : LevelLE W.R M (Hlow W H) H p where
  dvd := R_dvd W
  ddvd := ⟨1, by rw [Nat.div_eq_of_eq_mul_left W.R_pos W.hM, mul_one]⟩
  red u hu := Subgroup.mem_map_of_mem _ hu

theorem heckeDiagMatrix_mul_mapGL (hp : p ≠ 0) (γ : SL(2, ℤ)) (hγ : (p : ℤ) ∣ γ 1 0) :
    ModularForm.heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (conjLowerMat p γ hγ) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (ModularForm.heckeDiagMatrix p : Matrix (Fin 2) (Fin 2) ℝ) *
      ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    ((Matrix.SpecialLinearGroup.mapGL ℝ (conjLowerMat p γ hγ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      (ModularForm.heckeDiagMatrix p : Matrix (Fin 2) (Fin 2) ℝ)
  rw [ModularForm.val_heckeDiagMatrix hp, mapGL_coe_eq, mapGL_coe_eq]
  have hc : ((γ 1 0 / (p : ℤ) : ℤ) : ℝ) * (p : ℝ) = ((γ 1 0 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hγ
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, conjLowerMat, mul_comm]
  · rw [mul_comm]; exact hc.symm

variable [Fact p.Prime]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem le_conj_heckeDiagMatrix :
    Γ M H ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix p)⁻¹ • Γ W.R (Hlow W H) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨(iotaDeg W.R M (Hlow W H) H p (levelLE W) ⟨γ, hγ⟩ : SL(2, ℤ)), (iotaDeg W.R M (Hlow W H) H p (levelLE W) ⟨γ, hγ⟩).2, ?_⟩
  show (Matrix.SpecialLinearGroup.mapGL ℝ (conjLowerMat p γ ((levelLE W).dvd_entry ⟨γ, hγ⟩)) : GL (Fin 2) ℝ) =
    ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ * (ModularForm.heckeDiagMatrix p)⁻¹
  rw [heckeDiagMatrix_mul_mapGL hp γ, mul_inv_cancel_right]

private def _root_.AtkinLiRat.stretch : CuspForm (Γ W.R (Hlow W H)) k →ₗ[ℂ] CuspForm (Γ M H) k where
  toFun h := slashCusp (ModularForm.heckeDiagMatrix p) (le_conj_heckeDiagMatrix W) h
  map_add' f g := DFunLike.coe_injective <| by
    show ⇑(f + g) ∣[k] ModularForm.heckeDiagMatrix p =
      ⇑f ∣[k] ModularForm.heckeDiagMatrix p + ⇑g ∣[k] ModularForm.heckeDiagMatrix p
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show ⇑(c • f) ∣[k] ModularForm.heckeDiagMatrix p = c • (⇑f ∣[k] ModularForm.heckeDiagMatrix p)
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix]
    rfl

p2m_export "AtkinLiRat" "stretch"
@[scoped simp] theorem coe_stretch (h : CuspForm (Γ W.R (Hlow W H)) k) :
    ⇑(stretch W h : CuspForm (Γ M H) k) = ⇑h ∣[k] ModularForm.heckeDiagMatrix p := rfl

theorem coef_stretch (n : ℕ) (h : CuspForm (Γ W.R (Hlow W H)) k) :
    coef n (stretch W h : CuspForm (Γ M H) k) = (p : ℂ) ^ (k - 1) * (if p ∣ n then coef (n / p) h else 0) :=
  coef_of_coe_eq_slash_heckeDiagMatrix (Θ := stretch W h) (Φ := raise W h) (Fact.out : p.Prime).ne_zero rfl n

theorem IsRat.stretch {h : CuspForm (Γ W.R (Hlow W H)) k} (hh : IsRat h) : IsRat (stretch W h : CuspForm (Γ M H) k) := by
  intro n
  rw [coef_stretch]
  split_ifs with hpn
  · obtain ⟨r, hr⟩ := hh (n / p)
    refine ⟨(p : ℚ) ^ (k - 1) * r, ?_⟩
    rw [hr, Rat.cast_mul, Rat.cast_zpow, Rat.cast_natCast]
  · exact ⟨0, by simp⟩

theorem stretch_eq_raise {x y : CuspForm (Γ W.R (Hlow W H)) k} (h : stretch W x = (raise W y : CuspForm (Γ M H) k)) :
    x = 0 ∧ y = 0 := by
  have hp : p.Prime := Fact.out
  have hcoe : ⇑x ∣[k] ModularForm.heckeDiagMatrix p = ⇑y := congrArg (fun g : CuspForm (Γ M H) k => ⇑g) h
  have hle : ((Gamma1 W.R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ W.R (Hlow W H) :=
    Subgroup.map_mono Gamma1_le_GammaH
  have hx : restrictCusp hle x = 0 := by
    refine CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 hp (not_dvd_R W hp) k
      (restrictCusp hle x) fun γ hγ => ?_
    rw [coe_restrictCusp, hcoe]
    exact SlashInvariantFormClass.slash_action_eq y γ (hle hγ)
  have hcoex : (⇑x : ℍ → ℂ) = 0 := by
    have e := congrArg
      (fun g : CuspForm ((Gamma1 W.R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k => (⇑g : ℍ → ℂ)) hx
    simpa only [coe_restrictCusp, CuspForm.coe_zero] using e
  have hx0 : x = 0 := DFunLike.coe_injective (hcoex.trans CuspForm.coe_zero.symm)
  refine ⟨hx0, ?_⟩
  apply DFunLike.coe_injective
  rw [← hcoe, hcoex, CuspForm.coe_zero, SlashAction.zero_slash]

theorem stretch_injective : Function.Injective (stretch W : CuspForm (Γ W.R (Hlow W H)) k →ₗ[ℂ] CuspForm (Γ M H) k) := by
  intro x x' h
  have : stretch W (x - x') = (raise W 0 : CuspForm (Γ M H) k) := by rw [map_sub, h, sub_self, map_zero]
  exact sub_eq_zero.mp (stretch_eq_raise W this).1

theorem alLin_raise (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H)
    (h : CuspForm (Γ W.R (Hlow W H)) k) :
    alLin W hHp k (raise W h) = stretch W (CuspForm.diamondLinH k (pUnit W) h) := by
  apply DFunLike.coe_injective
  rw [coe_alLin, coe_raise, coe_stretch, ModularForm.alSlash_def,
    alGL_eq_gammaW_mul W (Fact.out : p.Prime).ne_zero, SlashAction.slash_mul,
    CuspForm.coe_diamondLinH_eq_slash k (CuspForm.stableD W.R (Hlow W H) k) (pUnit W) ⟨gammaW W, gammaW_mem W⟩
      (gamma0Units_gammaW W) h]

omit [Fact p.Prime] in

theorem diamondLinH_raise (e : (ZMod M)ˣ) (h : CuspForm (Γ W.R (Hlow W H)) k) :
    CuspForm.diamondLinH k e (raise W h : CuspForm (Γ M H) k) =
      raise W (CuspForm.diamondLinH k (ZMod.unitsMap (R_dvd W) e) h) := by
  apply DFunLike.coe_injective
  rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k) e, coe_raise, coe_raise,
    CuspForm.coe_diamondLinH_eq_slash k (CuspForm.stableD W.R (Hlow W H) k) (ZMod.unitsMap (R_dvd W) e)
      ⟨CuspForm.gammaLift M e, Gamma0_le_of_dvd (R_dvd W) (CuspForm.gammaLift M e).2⟩
      (by rw [← unitsMap_gamma0Units (R_dvd W), CuspForm.gamma0Units_gammaLift]) h]

def traceForm (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H) (φ : CuspForm (Γ M H) k) :
    CuspForm (Γ M H) k :=
  alLin W hHp k φ + CuspForm.heckeULinH k p φ

theorem traceForm_slash (hpM : p ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H)
    (φ : CuspForm (Γ M H) 2) :
    ∀ γ ∈ Γ W.R (Hlow W H), ⇑(traceForm W hHp φ) ∣[(2 : ℤ)] γ = ⇑(traceForm W hHp φ) := by
  have hp : p.Prime := Fact.out
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hg0, hgH⟩ := mem_GammaH_iff.mp hg
  obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp hgH
  have hcoe : ⇑(traceForm W hHp φ) = ModularForm.alSlash W 2 ⇑φ + ModularForm.heckeU 2 p ⇑φ := by
    rw [traceForm, CuspForm.coe_add, coe_alLin, CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hp hpM)]
  rw [hcoe]
  exact ModularForm.alSlash_add_heckeU_slash_eq_self_of_mem_GammaH hp W H hHp
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq φ γ hγ) g hg0 ⟨u, hu, hug⟩

def traceLow (hpM : p ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H)
    (φ : CuspForm (Γ M H) 2) : CuspForm (Γ W.R (Hlow W H)) 2 :=
  lower W (traceForm W hHp φ) (traceForm_slash W hpM hHp φ)

theorem raise_traceLow (hpM : p ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H)
    (φ : CuspForm (Γ M H) 2) : raise W (traceLow W hpM hHp φ) = traceForm W hHp φ :=
  raise_lower W _ _

end LevelPair

section Extract

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime] (W : ModularForm.AtkinLehnerDatum M p)

theorem extract {g : ℕ} (b : Module.Basis (Fin g) ℂ (CuspForm (Γ W.R (Hlow W H)) 2)) (hbrat : ∀ i, IsRat (b i))
    (x y : CuspForm (Γ W.R (Hlow W H)) 2) (r : CuspForm (Γ M H) 2) (hr : IsRat r)
    (h : stretch W x - raise W y = r) : IsRat x := by
  classical

  let w : Fin g ⊕ Fin g → CuspForm (Γ M H) 2 := Sum.elim (fun i => stretch W (b i)) (fun i => raise W (b i))
  have hw1 : LinearIndependent ℂ (fun i => stretch W (b i) : Fin g → CuspForm (Γ M H) 2) :=
    (b.linearIndependent.map' (stretch W) (LinearMap.ker_eq_bot.mpr (stretch_injective W)))
  have hw2 : LinearIndependent ℂ (fun i => raise W (b i) : Fin g → CuspForm (Γ M H) 2) :=
    (b.linearIndependent.map' (raise W) (LinearMap.ker_eq_bot.mpr (raise_injective W)))
  have hdisj : Disjoint (Submodule.span ℂ (Set.range fun i => (stretch W (b i) : CuspForm (Γ M H) 2)))
      (Submodule.span ℂ (Set.range fun i => (raise W (b i) : CuspForm (Γ M H) 2))) := by
    rw [Submodule.disjoint_def]
    intro v hv1 hv2
    rw [Set.range_comp' (stretch W) b, ← Submodule.map_span] at hv1
    rw [Set.range_comp' (raise W) b, ← Submodule.map_span] at hv2
    obtain ⟨a, -, rfl⟩ := Submodule.mem_map.mp hv1
    obtain ⟨c, -, hc⟩ := Submodule.mem_map.mp hv2
    have := (stretch_eq_raise W hc.symm).1
    rw [this, map_zero]
  have hw : LinearIndependent ℂ w := hw1.sum_type hw2 hdisj
  have hwrat : ∀ s, IsRat (w s) := by
    rintro (i | i)
    · exact IsRat.stretch W (hbrat i)
    · exact IsRat.raise W (hbrat i)

  obtain ⟨cx, rfl⟩ : ∃ c : Fin g → ℂ, x = ∑ i, c i • b i := ⟨fun i => b.repr x i, (b.sum_repr x).symm⟩
  obtain ⟨cy, rfl⟩ : ∃ c : Fin g → ℂ, y = ∑ i, c i • b i := ⟨fun i => b.repr y i, (b.sum_repr y).symm⟩
  let e : Fin g ⊕ Fin g → ℂ := Sum.elim cx (fun i => - cy i)
  have hre : r = ∑ s, e s • w s := by
    rw [← h, Fintype.sum_sum_type, map_sum, map_sum]
    simp only [e, w, Sum.elim_inl, Sum.elim_inr, _root_.neg_smul, Finset.sum_neg_distrib, map_smul,
      sub_eq_add_neg]
  have hmem : r ∈ Submodule.span ℂ (Set.range w) := by
    rw [hre]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  obtain ⟨q, hq⟩ := exists_rat_coord w hw hwrat r hr hmem

  have hzero : ∑ s, (e s - ((q s : ℚ) : ℂ)) • w s = 0 := by
    rw [Finset.sum_congr rfl fun s _ => sub_smul (e s) _ (w s), Finset.sum_sub_distrib, ← hre, ← hq, sub_self]
  have hcoord := Fintype.linearIndependent_iff.mp hw _ hzero
  have hcxq : ∀ i, cx i = ((q (Sum.inl i) : ℚ) : ℂ) := fun i => by
    have := hcoord (Sum.inl i)
    simp only [e, Sum.elim_inl] at this
    exact sub_eq_zero.mp this
  refine IsRat.of_eq_sum_ratSmul hbrat (fun i => q (Sum.inl i)) ?_
  exact Finset.sum_congr rfl fun i _ => by rw [hcxq]

end Extract

section Main

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime]

theorem isRat_alLin (hpM : p ∣ M) (W : ModularForm.AtkinLehnerDatum M p)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H)
    (f : CuspForm (Γ M H) 2) (hf : IsRat f) : IsRat (alLin W hHp 2 f) := by
  have hp : p.Prime := Fact.out

  set U : CuspForm (Γ M H) 2 →ₗ[ℂ] CuspForm (Γ M H) 2 := CuspForm.heckeULinH 2 p with hU
  set Dp : CuspForm (Γ W.R (Hlow W H)) 2 →ₗ[ℂ] CuspForm (Γ W.R (Hlow W H)) 2 :=
    CuspForm.diamondLinH 2 (pUnit W) with hDp

  set h : CuspForm (Γ W.R (Hlow W H)) 2 := traceLow W hpM hHp f with hh
  set h₂ : CuspForm (Γ W.R (Hlow W H)) 2 := traceLow W hpM hHp (U f) with hh₂
  have hG : raise W h = alLin W hHp 2 f + U f := raise_traceLow W hpM hHp f
  have hG₂ : raise W h₂ = alLin W hHp 2 (U f) + U (U f) := raise_traceLow W hpM hHp (U f)

  have hkey : stretch W (Dp h) - raise W h₂ =
      CuspForm.diamondLinH 2 (sqUnitU W) f - U (U f) := by
    rw [hDp, ← alLin_raise W hHp h, hG, map_add, alLin_alLin_two W hHp f, hG₂]
    abel

  have hr : IsRat (CuspForm.diamondLinH 2 (sqUnitU W) f - U (U f)) := by
    refine IsRat.sub ?_ ((hf.heckeULinH hp hpM).heckeULinH hp hpM)
    exact isRat_of_mem_heckeRingH (CuspForm.heckeGenH_mem_heckeRingH ∅ 2 (Gen.dia (sqUnitU W))) hf

  obtain ⟨b, hb⟩ := exists_basis_heckeIntegral W.R (Hlow W H)
  have hbrat : ∀ i, IsRat (b i) := fun i => IsRat.of_intCast fun n => by
    obtain ⟨a, ha⟩ := hb i 1 (Subring.one_mem _) n
    exact ⟨a, by simpa using ha⟩

  have hDph : IsRat (Dp h) := extract W b hbrat (Dp h) h₂ _ hr hkey

  obtain ⟨e, he⟩ := ZMod.unitsMap_surjective (R_dvd W) (pUnit W)⁻¹
  have htrans : CuspForm.diamondLinH 2 e (raise W (Dp h) : CuspForm (Γ M H) 2) = raise W h := by
    rw [diamondLinH_raise W e, he, hDp, diamondLinH_inv_apply]
  have hGrat : IsRat (raise W h : CuspForm (Γ M H) 2) := by
    rw [← htrans]
    exact isRat_of_mem_heckeRingH (CuspForm.heckeGenH_mem_heckeRingH ∅ 2 (Gen.dia e)) (IsRat.raise W hDph)

  have hWf : alLin W hHp 2 f = raise W h - U f := by rw [hG, add_sub_cancel_right]
  rw [hWf]
  exact hGrat.sub (hf.heckeULinH hp hpM)

omit [NeZero M] [Fact p.Prime] in
theorem R_eq (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p) : M / p = W.R :=
  Nat.div_eq_of_eq_mul_right hp.pos W.hM

theorem main (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (f : CuspForm (GammaH M H) 2)
    (hf : ∀ n : ℕ, ∃ r : ℚ, ModularFormClass.qCoeff (⇑f) n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑f) n = (r : ℂ) := by
  have hp : p.Prime := Fact.out
  have hHpW : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H :=
    hHp_transfer (Nat.div_dvd_of_dvd hpM) (R_dvd W) (R_eq hp W) hHp
  obtain ⟨r, hr⟩ := isRat_alLin hpM W hHpW f hf n
  exact ⟨r, hr⟩

end Main

end AtkinLiRat
p2m_reactivate "P2MW.S_CuspForm_exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH.AtkinLiRat"

end
p2m_reactivate "P2MW.S_CuspForm_exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH.AtkinLiRat"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ n : ℕ, ∃ r : ℚ, ModularFormClass.qCoeff (⇑f) n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑f) n = (r : ℂ) :=
  AtkinLiRat.main hpM hHp W f hf n

end S_CuspForm_exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH
end P2MW
export P2MW.S_CuspForm_exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH (solution)
