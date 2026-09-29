-- Prove2me | solution 1 for CuspForm.TWLevel.HeckeRing.exists_isEigenformWith_or_eisenstein_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e21090bb-9bab-501a-b11c-5458e641300d

import Definitions.Def_CuspForm_TWLevelHeckeRing
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CohCarrier_HeckeDiamondRing
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector
import Theorems.Thm_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
import Theorems.Thm_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
import Theorems.Thm_CuspForm_IsEigenformWith_fg_adjoin_qCoeff
import Theorems.Thm_IntegralClosure_exists_extend_ringHom_dvr_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_HeckeRing_exists_isEigenformWith_or_eisenstein_of_algHom
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex CuspForm.GammaH_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id"
p2m_attr_erase "simp" "ModularCurve.coeffMap_single"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open IsLocalRing

noncomputable section

namespace ClassicalityAsm

section Bridge

variable {B : Type} [Ring B]
  {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
  [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']

omit [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] [IsAdicComplete (maximalIdeal 𝒪') 𝒪']
  [Finite (ResidueField 𝒪')] [CharZero 𝒪'] in
theorem apply_eq_of_apply_eq (χ : B →+* ℂ) (μ : B →+* 𝒪')
    (hker : ∀ b : B, χ b = 0 ↔ μ b = 0) {b b' : B} (h : χ b = χ b') : μ b = μ b' := by
  have : μ (b - b') = 0 := by
    rw [← hker, map_sub, h, sub_self]
  rwa [map_sub, sub_eq_zero] at this

def liftVal (χ : B →+* ℂ) (μ : B →+* 𝒪') (y : ℂ) (hy : y ∈ Set.range χ) : 𝒪' := μ hy.choose

omit [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] [IsAdicComplete (maximalIdeal 𝒪') 𝒪']
  [Finite (ResidueField 𝒪')] [CharZero 𝒪'] in
theorem liftVal_eq (χ : B →+* ℂ) (μ : B →+* 𝒪') (hker : ∀ b : B, χ b = 0 ↔ μ b = 0)
    {y : ℂ} (hy : y ∈ Set.range χ) {b : B} (hb : χ b = y) : liftVal χ μ y hy = μ b :=
  apply_eq_of_apply_eq χ μ hker (hy.choose_spec.trans hb.symm)

theorem bridge (χ : B →+* ℂ) (μ : B →+* 𝒪') (hker : ∀ b : B, χ b = 0 ↔ μ b = 0)
    (A : Subalgebra ℤ ℂ) (hAfg : (Subalgebra.toSubmodule A).FG) (hχA : ∀ b : B, χ b ∈ A) :
    ∃ (𝒪₁ : Type) (_ : CommRing 𝒪₁) (_ : IsDomain 𝒪₁) (_ : IsDiscreteValuationRing 𝒪₁)
      (_ : IsAdicComplete (maximalIdeal 𝒪₁) 𝒪₁) (_ : Finite (ResidueField 𝒪₁)) (_ : CharZero 𝒪₁)
      (_ : Algebra 𝒪' 𝒪₁) (_ : Module.Finite 𝒪' 𝒪₁) (_ : IsLocalHom (algebraMap 𝒪' 𝒪₁)),
      Function.Injective (algebraMap 𝒪' 𝒪₁) ∧
      ∃ ι : ↥A →+* 𝒪₁, ∀ b : B, ι ⟨χ b, hχA b⟩ = algebraMap 𝒪' 𝒪₁ (μ b) := by
  classical
  have hAint : ∀ x ∈ A, IsIntegral ℤ x := IsIntegral.of_mem_of_fg A hAfg
  set Z : Subalgebra ℤ ℂ := integralClosure ℤ ℂ with hZ

  let R : Subalgebra ℤ ↥Z := (χ.toIntAlgHom.range).comap Z.val
  have hmemR : ∀ z : ↥Z, z ∈ R ↔ (z : ℂ) ∈ Set.range χ := fun z => by
    show Z.val z ∈ χ.toIntAlgHom.range ↔ _
    rw [AlgHom.mem_range]
    rfl

  let φR : ↥R →+* 𝒪' :=
    { toFun := fun z => liftVal χ μ ((z : ↥Z) : ℂ) ((hmemR z.1).mp z.2)
      map_one' := (liftVal_eq χ μ hker _ (b := 1) (by rw [map_one]; rfl)).trans (map_one μ)
      map_mul' := fun z w => by
        obtain ⟨bz, hbz⟩ := (hmemR z.1).mp z.2
        obtain ⟨bw, hbw⟩ := (hmemR w.1).mp w.2
        rw [liftVal_eq χ μ hker _ hbz, liftVal_eq χ μ hker _ hbw,
          liftVal_eq χ μ hker _ (b := bz * bw) (by rw [map_mul, hbz, hbw]; rfl), map_mul]
      map_zero' := (liftVal_eq χ μ hker _ (b := 0) (by rw [map_zero]; rfl)).trans (map_zero μ)
      map_add' := fun z w => by
        obtain ⟨bz, hbz⟩ := (hmemR z.1).mp z.2
        obtain ⟨bw, hbw⟩ := (hmemR w.1).mp w.2
        rw [liftVal_eq χ μ hker _ hbz, liftVal_eq χ μ hker _ hbw,
          liftVal_eq χ μ hker _ (b := bz + bw) (by rw [map_add, hbz, hbw]; rfl), map_add] }

  obtain ⟨tA, htA⟩ := Subalgebra.fg_of_fg_toSubmodule hAfg
  have htA_mem : ∀ x ∈ tA, x ∈ A := fun x hx => by
    rw [← htA]; exact Algebra.subset_adjoin hx
  let s : Finset ↥Z := tA.attach.image fun x => ⟨x.1, hAint x.1 (htA_mem x.1 x.2)⟩

  obtain ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, -, hinj, φ', hφ'⟩ :=
    IntegralClosure.exists_extend_ringHom_dvr_finite (𝒪' := 𝒪') (p := 0)
      (by rw [Nat.cast_zero]; exact zero_mem _) R s φR

  have hmem : ∀ (x : ℂ) (hx : x ∈ A),
      (⟨x, hAint x hx⟩ : ↥Z) ∈ R ⊔ Algebra.adjoin ℤ (↑s : Set ↥Z) := by
    intro x hx
    have hx' : x ∈ Algebra.adjoin ℤ (↑tA : Set ℂ) := by rw [htA]; exact hx
    suffices h : ∀ hxZ : IsIntegral ℤ x, (⟨x, hxZ⟩ : ↥Z) ∈ R ⊔ Algebra.adjoin ℤ (↑s : Set ↥Z) from
      h _
    clear hx
    induction hx' using Algebra.adjoin_induction with
    | mem y hy =>
      intro hyZ
      apply (le_sup_right : Algebra.adjoin ℤ (↑s : Set ↥Z) ≤ R ⊔ Algebra.adjoin ℤ (↑s : Set ↥Z))
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩
    | algebraMap n =>
      intro hnZ
      have : (⟨algebraMap ℤ ℂ n, hnZ⟩ : ↥Z) = algebraMap ℤ ↥Z n := Subtype.ext (by simp)
      rw [this]
      exact Subalgebra.algebraMap_mem _ n
    | add y z hy hz ihy ihz =>
      intro hZ'
      have hyA : y ∈ A := by rw [← htA]; exact hy
      have hzA : z ∈ A := by rw [← htA]; exact hz
      have : (⟨y + z, hZ'⟩ : ↥Z) = ⟨y, hAint y hyA⟩ + ⟨z, hAint z hzA⟩ := rfl
      rw [this]
      exact add_mem (ihy _) (ihz _)
    | mul y z hy hz ihy ihz =>
      intro hZ'
      have hyA : y ∈ A := by rw [← htA]; exact hy
      have hzA : z ∈ A := by rw [← htA]; exact hz
      have : (⟨y * z, hZ'⟩ : ↥Z) = ⟨y, hAint y hyA⟩ * ⟨z, hAint z hzA⟩ := rfl
      rw [this]
      exact mul_mem (ihy _) (ihz _)

  let ιf : ↥A → 𝒪₁ := fun x => φ' ⟨⟨x.1, hAint x.1 x.2⟩, hmem x.1 x.2⟩
  have hιf : ∀ x : ↥A, ιf x = φ' ⟨⟨x.1, hAint x.1 x.2⟩, hmem x.1 x.2⟩ := fun _ => rfl
  let ι : ↥A →+* 𝒪₁ :=
    { toFun := ιf
      map_one' := by
        rw [hιf, ← map_one φ']
        rfl
      map_mul' := fun x y => by
        rw [hιf, hιf, hιf, ← map_mul]
        rfl
      map_zero' := by
        rw [hιf, ← map_zero φ']
        rfl
      map_add' := fun x y => by
        rw [hιf, hιf, hιf, ← map_add]
        rfl }
  refine ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj, ι, fun b => ?_⟩
  have hR : (⟨χ b, hAint _ (hχA b)⟩ : ↥Z) ∈ R := (hmemR _).mpr ⟨b, rfl⟩
  have h1 : (⟨⟨χ b, hAint _ (hχA b)⟩, hmem _ (hχA b)⟩ : ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set ↥Z))) =
      Subalgebra.inclusion le_sup_left ⟨_, hR⟩ := Subtype.ext rfl
  show φ' _ = _
  rw [h1, hφ']
  congr 1
  exact liftVal_eq χ μ hker _ rfl

end Bridge

section Loc

open CuspForm.TWLevel CohCarrier

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ) [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* ResidueField 𝒪) (α : Fin t → ResidueField 𝒪)
  (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)

abbrev Cen : Subalgebra ℤ (Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪)) :=
  Subalgebra.centralizer ℤ (Set.range (op N r qv S 𝒪 H))

omit [NeZero N] [NeZero r] [IsLocalRing 𝒪] in
theorem mem_Cen_iff (b : Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪)) :
    b ∈ Cen N r qv S 𝒪 H ↔ ∀ g, op N r qv S 𝒪 H g * b = b * op N r qv S 𝒪 H g := by
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro h g
    exact h _ ⟨g, rfl⟩
  · rintro h _ ⟨g, rfl⟩
    exact h g

omit [NeZero r] in

theorem opAlgHom_comm {b : Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪)}
    (hb : b ∈ Cen N r qv S 𝒪 H) (f : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) :
    b * (heckeData N r qv S 𝒪 H θ α hc).opAlgHom f =
      (heckeData N r qv S 𝒪 H θ α hc).opAlgHom f * b := by
  rw [mem_Cen_iff] at hb
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [show (MvPolynomial.C a : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) =
      algebraMap 𝒪 (heckeData N r qv S 𝒪 H θ α hc).FreeAlg a from rfl, AlgHom.commutes]
    exact (Algebra.commutes a b).symm
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | mul_X p g hp =>
    rw [map_mul, CohCarrier.HeckeData.opAlgHom_X, ← mul_assoc, hp, mul_assoc,
      show (heckeData N r qv S 𝒪 H θ α hc).op g = op N r qv S 𝒪 H g from rfl, ← hb g, ← mul_assoc]

def linOf (b : Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪)) (hb : b ∈ Cen N r qv S 𝒪 H) :
    Carrier N r qv 𝒪 H →ₗ[(heckeData N r qv S 𝒪 H θ α hc).FreeAlg] Carrier N r qv 𝒪 H where
  toFun := b
  map_add' := map_add b
  map_smul' f v := by
    show b ((heckeData N r qv S 𝒪 H θ α hc).opAlgHom f v) =
      (heckeData N r qv S 𝒪 H θ α hc).opAlgHom f (b v)
    exact congrArg (fun T : Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪) => T v)
      (opAlgHom_comm N r qv S 𝒪 H θ α hc hb f)

def locEnd (b : Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪)) (hb : b ∈ Cen N r qv S 𝒪 H) :
    Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) :=
  ((LocalizedModule.map (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl
      (linOf N r qv S 𝒪 H θ α hc b hb)).restrictScalars
        (heckeData N r qv S 𝒪 H θ α hc).FreeAlg).restrictScalars 𝒪

omit [NeZero r] in
theorem locEnd_mk (b : Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪)) (hb : b ∈ Cen N r qv S 𝒪 H)
    (m : Carrier N r qv 𝒪 H) (s : ↥(heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl) :
    locEnd N r qv S 𝒪 H θ α hc b hb (LocalizedModule.mk m s) = LocalizedModule.mk (b m) s := by
  show LocalizedModule.map _ (linOf N r qv S 𝒪 H θ α hc b hb) (LocalizedModule.mk m s) = _
  rw [LocalizedModule.map_mk]
  rfl

def locHom : ↥(Cen N r qv S 𝒪 H) →+* Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) where
  toFun b := locEnd N r qv S 𝒪 H θ α hc b.1 b.2
  map_one' := by
    apply LinearMap.ext
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s => rw [locEnd_mk]; rfl
  map_mul' b c := by
    apply LinearMap.ext
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s => rw [Module.End.mul_apply, locEnd_mk, locEnd_mk, locEnd_mk]; rfl
  map_zero' := by
    apply LinearMap.ext
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [locEnd_mk, LinearMap.zero_apply]
      exact LocalizedModule.zero_mk s
  map_add' b c := by
    apply LinearMap.ext
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [LinearMap.add_apply, locEnd_mk, locEnd_mk, locEnd_mk, LocalizedModule.mk_add_mk,
        ← smul_add, LocalizedModule.mk_cancel_common_left]
      rfl

omit [NeZero r] in
theorem locHom_apply_mk (b : ↥(Cen N r qv S 𝒪 H)) (m : Carrier N r qv 𝒪 H)
    (s : ↥(heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl) :
    locHom N r qv S 𝒪 H θ α hc b (LocalizedModule.mk m s) =
      LocalizedModule.mk ((b : Module.End 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪)) m) s :=
  locEnd_mk N r qv S 𝒪 H θ α hc b.1 b.2 m s

omit [NeZero r] in

theorem locHom_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv)
    (hmem : (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL (level N r qv) H 𝒪 ℓ) ∈ Cen N r qv S 𝒪 H) :
    locHom N r qv S 𝒪 H θ α hc ⟨_, hmem⟩ =
      opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL)) := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [locHom_apply_mk, opML_apply, LocalizedModule.smul'_mk]
    congr 1
    change _ = (heckeData N r qv S 𝒪 H θ α hc).opAlgHom (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL)) m
    rw [CohCarrier.HeckeData.opAlgHom_X]
    rfl

theorem locHom_diamond (u : (ZMod (level N r qv))ˣ)
    (hmem : diamondL (level N r qv) H 𝒪 u ∈ Cen N r qv S 𝒪 H) :
    locHom N r qv S 𝒪 H θ α hc ⟨_, hmem⟩ = diaML N r qv S 𝒪 H θ α hc hdc u := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [locHom_apply_mk]
    show _ = LocalizedModule.map _ (diamondLin N r qv S 𝒪 H θ α hc hdc u) (LocalizedModule.mk m s)
    rw [LocalizedModule.map_mk]
    rfl

include hc hdc in
omit [IsLocalRing 𝒪] in
theorem gens_subset_Cen :
    heckeDiamondGens (level N r qv) H S (HR N r qv) 𝒪 ⊆ ↑(Cen N r qv S 𝒪 H) := by
  rintro _ (⟨ℓ, rfl⟩ | ⟨u, rfl⟩)
  · rw [SetLike.mem_coe, mem_Cen_iff]
    intro g
    exact hc g (Gen.T ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)
  · rw [SetLike.mem_coe, mem_Cen_iff]
    intro g
    exact (hdc u g).symm

include hc hdc in
omit [IsLocalRing 𝒪] in
theorem hDR_le_Cen : heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪 ≤ Cen N r qv S 𝒪 H :=
  Algebra.adjoin_le (gens_subset_Cen N r qv S 𝒪 H hc hdc)

include hdc in

def β₀ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪) →+*
    Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) :=
  (locHom N r qv S 𝒪 H θ α hc).comp
    (Subalgebra.inclusion (hDR_le_Cen N r qv S 𝒪 H hc hdc)).toRingHom

theorem β₀_apply (x : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) :
    β₀ N r qv S 𝒪 H θ α hc hdc x =
      locHom N r qv S 𝒪 H θ α hc ⟨x.1, hDR_le_Cen N r qv S 𝒪 H hc hdc x.2⟩ := rfl

theorem β₀_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv) :
    β₀ N r qv S 𝒪 H θ α hc hdc (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ hℓ hℓS hℓL) =
      opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL)) := by
  rw [β₀_apply]
  exact locHom_T N r qv S 𝒪 H θ α hc ℓ hℓ hℓS hℓL _

theorem β₀_diamond (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    β₀ N r qv S 𝒪 H θ α hc hdc (heckeDiamondRing.diamond (level N r qv) H S (HR N r qv) 𝒪 u hu) =
      diaML N r qv S 𝒪 H θ α hc hdc u := by
  rw [β₀_apply]
  exact locHom_diamond N r qv S 𝒪 H θ α hc hdc u _

theorem β₀_mem (x : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) :
    β₀ N r qv S 𝒪 H θ α hc hdc x ∈ heckeSubalgebra N r qv S 𝒪 H θ α hc hdc := by
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ⟨ℓ, rfl⟩ | ⟨u, rfl⟩
    · show β₀ N r qv S 𝒪 H θ α hc hdc
          (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2) ∈ _
      rw [β₀_T]
      exact Algebra.subset_adjoin (Or.inl ⟨ℓ.1, ℓ.2.1, ℓ.2.2.1, ℓ.2.2.2, rfl⟩)
    · show β₀ N r qv S 𝒪 H θ α hc hdc
          (heckeDiamondRing.diamond (level N r qv) H S (HR N r qv) 𝒪 u.1 u.2) ∈ _
      rw [β₀_diamond]
      exact Algebra.subset_adjoin (Or.inr ⟨u.1, u.2, rfl⟩)
  | algebraMap n =>
    rw [show (⟨algebraMap ℤ _ n, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) =
        algebraMap ℤ _ n from rfl, eq_intCast, map_intCast]
    exact Subalgebra.intCast_mem _ n
  | add y z hy hz ihy ihz =>
    rw [show (⟨y + z, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) = ⟨y, hy⟩ + ⟨z, hz⟩
        from rfl, map_add]
    exact add_mem ihy ihz
  | mul y z hy hz ihy ihz =>
    rw [show (⟨y * z, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) = ⟨y, hy⟩ * ⟨z, hz⟩
        from rfl, map_mul]
    exact mul_mem ihy ihz

def β : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪) →+* HeckeRing N r qv S 𝒪 H θ α hc hdc where
  toFun x := ⟨β₀ N r qv S 𝒪 H θ α hc hdc x, β₀_mem N r qv S 𝒪 H θ α hc hdc x⟩
  map_one' := HeckeRing.ext N r qv S 𝒪 H θ α hc hdc (by
    show β₀ N r qv S 𝒪 H θ α hc hdc 1 = HeckeRing.act N r qv S 𝒪 H θ α hc hdc 1
    rw [map_one, map_one])
  map_mul' x y := HeckeRing.ext N r qv S 𝒪 H θ α hc hdc (by
    show β₀ N r qv S 𝒪 H θ α hc hdc (x * y) = HeckeRing.act N r qv S 𝒪 H θ α hc hdc (_ * _)
    rw [map_mul, map_mul]
    rfl)
  map_zero' := HeckeRing.ext N r qv S 𝒪 H θ α hc hdc (by
    show β₀ N r qv S 𝒪 H θ α hc hdc 0 = HeckeRing.act N r qv S 𝒪 H θ α hc hdc 0
    rw [map_zero, map_zero])
  map_add' x y := HeckeRing.ext N r qv S 𝒪 H θ α hc hdc (by
    show β₀ N r qv S 𝒪 H θ α hc hdc (x + y) = HeckeRing.act N r qv S 𝒪 H θ α hc hdc (_ + _)
    rw [map_add, map_add]
    rfl)

theorem act_β (x : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) :
    HeckeRing.act N r qv S 𝒪 H θ α hc hdc (β N r qv S 𝒪 H θ α hc hdc x) =
      β₀ N r qv S 𝒪 H θ α hc hdc x := rfl

theorem β_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv) :
    β N r qv S 𝒪 H θ α hc hdc (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ hℓ hℓS hℓL) =
      HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL :=
  HeckeRing.ext N r qv S 𝒪 H θ α hc hdc (by
    rw [act_β, HeckeRing.act_T]
    exact β₀_T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL)

theorem β_diamond (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    β N r qv S 𝒪 H θ α hc hdc (heckeDiamondRing.diamond (level N r qv) H S (HR N r qv) 𝒪 u hu) =
      HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu :=
  HeckeRing.ext N r qv S 𝒪 H θ α hc hdc (by
    rw [act_β, HeckeRing.act_diamond]
    exact β₀_diamond N r qv S 𝒪 H θ α hc hdc u hu)

include hc hdc in
omit [IsLocalRing 𝒪] in

theorem gens_comm :
    ∀ a ∈ heckeDiamondGens (level N r qv) H S (HR N r qv) 𝒪,
      ∀ b ∈ heckeDiamondGens (level N r qv) H S (HR N r qv) 𝒪, a * b = b * a := by
  rintro a (⟨ℓ, rfl⟩ | ⟨u, rfl⟩) b (⟨ℓ', rfl⟩ | ⟨v, rfl⟩)
  · exact hc (Gen.T ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2) (Gen.T ℓ'.1 ℓ'.2.1 ℓ'.2.2.1 ℓ'.2.2.2)
  · exact (hdc v (Gen.T ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)).symm
  · exact hdc u (Gen.T ℓ'.1 ℓ'.2.1 ℓ'.2.2.1 ℓ'.2.2.2)
  · exact diamondL_comm (level N r qv) H 𝒪 u v

end Loc

section Chars

theorem isIntegral_dirichletCharacter_units {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (u : (ZMod M)ˣ) : IsIntegral ℤ (ψ (u : ZMod M)) := by
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  obtain ⟨n, hn, hun⟩ := hfin.exists_pow_eq_one
  have hpow : (ψ (u : ZMod M)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hun, Units.val_one, map_one]
  refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C (1 : ℤ) hn.ne', ?_⟩
  simp [hpow]

end Chars

section Main

open CuspForm.TWLevel CohCarrier

set_option maxHeartbeats 12800000 in
theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] 𝒪') :
    ∃ (𝒪₁ : Type) (_ : CommRing 𝒪₁) (_ : IsDomain 𝒪₁) (_ : IsDiscreteValuationRing 𝒪₁)
      (_ : IsAdicComplete (maximalIdeal 𝒪₁) 𝒪₁) (_ : Finite (ResidueField 𝒪₁)) (_ : CharZero 𝒪₁)
      (_ : Algebra 𝒪' 𝒪₁) (_ : Module.Finite 𝒪' 𝒪₁) (_ : IsLocalHom (algebraMap 𝒪' 𝒪₁)),
      Function.Injective (algebraMap 𝒪' 𝒪₁) ∧
      ((∃ (ε : DirichletCharacter ℂ (level N r qv))
          (h : CuspForm (CongruenceSubgroup.Gamma1 (level N r qv)) 2)
          (ι : Algebra.adjoin ℤ ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
              Set.range fun u : (ZMod (level N r qv))ˣ => ε (u : ZMod (level N r qv))) →+* 𝒪₁),
          CuspForm.IsEigenformWith ε h ∧
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H → ε (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ModularFormClass.qCoeff h ℓ, Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ε (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu)))) ∨
       (∃ (ψ₁ ψ₂ : DirichletCharacter ℂ (level N r qv))
          (ι : Algebra.adjoin ℤ
              ((Set.range fun u : (ZMod (level N r qv))ˣ => ψ₁ (u : ZMod (level N r qv))) ∪
                Set.range fun u : (ZMod (level N r qv))ˣ => ψ₂ (u : ZMod (level N r qv))) →+* 𝒪₁),
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H →
            ψ₁ (u : ZMod (level N r qv)) * ψ₂ (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)),
                Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)⟩ +
              (ℓ : 𝒪₁) * ι ⟨ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) :
                  ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ψ₁ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)⟩ *
                ι ⟨ψ₂ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu))))) := by
  classical

  let μ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪) →+* 𝒪' :=
    lam.toRingHom.comp (β N r qv S 𝒪 H θ α hc hdc)
  have hμT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ (level N r qv)),
      μ (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ hℓ hℓS hℓL) =
        lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL) := by
    intro ℓ hℓ hℓS hℓL
    show lam (β N r qv S 𝒪 H θ α hc hdc _) = _
    rw [β_T]
  have hμD : ∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
      μ (heckeDiamondRing.diamond (level N r qv) H S (HR N r qv) 𝒪 u hu) =
        lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu) := by
    intro u hu
    show lam (β N r qv S 𝒪 H θ α hc hdc _) = _
    rw [β_diamond]

  haveI hprime : (RingHom.ker μ).IsPrime := RingHom.ker_isPrime μ
  have hkerZ : ∀ n : ℤ, (n : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) ∈ RingHom.ker μ → n = 0 := by
    intro n hn
    rw [RingHom.mem_ker, map_intCast] at hn
    exact_mod_cast hn

  obtain ⟨χ, e, φ, hker, hφ0, hTφ, hDφ, heχ⟩ :=
    CohCarrier.heckeDiamondRing.exists_ringHom_ker_eq_eigenvector (𝒪 := 𝒪) (level N r qv) H S (HR N r qv)
      (gens_comm N r qv S 𝒪 H hc hdc) (RingHom.ker μ) hkerZ ℂ
  have hker' : ∀ b, χ b = 0 ↔ μ b = 0 := fun b => by
    rw [← RingHom.mem_ker, hker, RingHom.mem_ker]

  have heH : ∀ u : (ZMod (level N r qv))ˣ, u ∈ H → e u = 1 := by
    intro u hu
    have h1 := hDφ u
    rw [CohCarrier.diamondL_of_mem (level N r qv) H ℂ u hu, Module.End.one_apply] at h1
    have h2 : ((e u : ℂ) - 1) • φ = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact Units.val_eq_one.mp (sub_eq_zero.mp h3)
    · exact absurd h3 hφ0

  let a : ℕ → ℂ := fun ℓ =>
    if h : ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ (level N r qv) then χ (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ h.1 h.2.1 h.2.2)
    else 0
  have ha : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ (level N r qv)),
      a ℓ = χ (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ hℓ hℓS hℓL) := by
    intro ℓ hℓ hℓS hℓL
    show (if h : ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ (level N r qv) then _ else _) = _
    rw [dif_pos ⟨hℓ, hℓS, hℓL⟩]
  have hT' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ (level N r qv) →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (level N r qv) H ℓ ℂ φ) = a ℓ • φ := by
    intro ℓ hℓ hℓS hℓL
    rw [ha ℓ hℓ hℓS hℓL]
    exact hTφ ℓ hℓ hℓS hℓL
  by_cases hpar : φ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH (level N r qv) H) ℂ
  ·
    obtain ⟨ε, h, hEig, hεe, hqa⟩ :=
      CohCarrier.exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul (level N r qv) H S φ hpar hφ0 a e
        hT' hDφ
    let A : Subalgebra ℤ ℂ := Algebra.adjoin ℤ
      ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
        Set.range fun u : (ZMod (level N r qv))ˣ => ε (u : ZMod (level N r qv)))
    have hAfg : (Subalgebra.toSubmodule A).FG := hEig.fg_adjoin_qCoeff

    have hχA : ∀ b : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪), χ b ∈ A := by
      rintro ⟨b, hb⟩
      induction hb using Algebra.adjoin_induction with
      | mem y hy =>
        rcases hy with ⟨ℓ, rfl⟩ | ⟨u, rfl⟩
        · have : χ ⟨heckeTFamily (level N r qv) H S 𝒪 ℓ, Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)⟩ =
              ModularFormClass.qCoeff h ℓ.1 := by
            rw [hqa ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2, ha ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2]
            rfl
          rw [this]
          exact Algebra.subset_adjoin (Or.inl ⟨ℓ.1, rfl⟩)
        · have : χ ⟨diamondL (level N r qv) H 𝒪 u, Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ = ε (u.1 : ZMod (level N r qv)) := by
            rw [hεe u.1, heχ u.1 u.2]
            rfl
          rw [this]
          exact Algebra.subset_adjoin (Or.inr ⟨u.1, rfl⟩)
      | algebraMap n =>
        rw [show (⟨algebraMap ℤ _ n, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) =
            algebraMap ℤ _ n from rfl, eq_intCast, map_intCast]
        exact Subalgebra.intCast_mem _ n
      | add y z hy hz ihy ihz =>
        rw [show (⟨y + z, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) = ⟨y, hy⟩ + ⟨z, hz⟩
            from rfl, map_add]
        exact add_mem ihy ihz
      | mul y z hy hz ihy ihz =>
        rw [show (⟨y * z, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) = ⟨y, hy⟩ * ⟨z, hz⟩
            from rfl, map_mul]
        exact mul_mem ihy ihz
    obtain ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj, ι, hι⟩ :=
      bridge (B := ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) χ μ hker' A hAfg hχA
    refine ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj, Or.inl ⟨ε, h, ι, hEig, ?_, ?_, ?_⟩⟩
    · intro u hu
      rw [hεe u, heH u hu, Units.val_one]
    · intro ℓ hℓ hℓS hℓL
      have h1 : (⟨ModularFormClass.qCoeff h ℓ, Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)⟩ : ↥A) =
          ⟨χ (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ hℓ hℓS hℓL), hχA _⟩ :=
        Subtype.ext ((hqa ℓ hℓ hℓS hℓL).trans (ha ℓ hℓ hℓS hℓL))
      rw [h1, hι, hμT]
    · intro u hu
      have h1 : (⟨ε (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ : ↥A) =
          ⟨χ (heckeDiamondRing.diamond (level N r qv) H S (HR N r qv) 𝒪 u hu), hχA _⟩ :=
        Subtype.ext ((hεe u).trans (heχ u hu))
      rw [h1, hι, hμD]
  ·
    obtain ⟨ψ₁, ψ₂, hψe, haψ⟩ :=
      CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul (level N r qv) H S φ
        hpar a e hT' hDφ
    let A : Subalgebra ℤ ℂ := Algebra.adjoin ℤ
      ((Set.range fun u : (ZMod (level N r qv))ˣ => ψ₁ (u : ZMod (level N r qv))) ∪
        Set.range fun u : (ZMod (level N r qv))ˣ => ψ₂ (u : ZMod (level N r qv)))
    have hAfg : (Subalgebra.toSubmodule A).FG := by
      apply fg_adjoin_of_finite ((Set.finite_range _).union (Set.finite_range _))
      rintro x (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · exact isIntegral_dirichletCharacter_units ψ₁ u
      · exact isIntegral_dirichletCharacter_units ψ₂ u
    have hψ₁A : ∀ u : (ZMod (level N r qv))ˣ, ψ₁ (u : ZMod (level N r qv)) ∈ A := fun u =>
      Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)
    have hψ₂A : ∀ u : (ZMod (level N r qv))ˣ, ψ₂ (u : ZMod (level N r qv)) ∈ A := fun u =>
      Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)

    have hχT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ (level N r qv)),
        χ (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ hℓ hℓS hℓL) =
          ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)) +
            (ℓ : ℂ) * ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)) := by
      intro ℓ hℓ hℓS hℓL
      rw [← ha ℓ hℓ hℓS hℓL, haψ ℓ hℓ hℓS hℓL, ZMod.coe_unitOfCoprime]
    have hχA : ∀ b : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪), χ b ∈ A := by
      rintro ⟨b, hb⟩
      induction hb using Algebra.adjoin_induction with
      | mem y hy =>
        rcases hy with ⟨ℓ, rfl⟩ | ⟨u, rfl⟩
        · have : χ ⟨heckeTFamily (level N r qv) H S 𝒪 ℓ, Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)⟩ =
              χ (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2) := rfl
          rw [this, hχT ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2]
          exact add_mem (hψ₁A _) (mul_mem (Subalgebra.natCast_mem _ _) (hψ₂A _))
        · have : χ ⟨diamondL (level N r qv) H 𝒪 u, Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              ψ₁ (u.1 : ZMod (level N r qv)) * ψ₂ (u.1 : ZMod (level N r qv)) := by
            rw [hψe u.1, heχ u.1 u.2]
            rfl
          rw [this]
          exact mul_mem (hψ₁A _) (hψ₂A _)
      | algebraMap n =>
        rw [show (⟨algebraMap ℤ _ n, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) =
            algebraMap ℤ _ n from rfl, eq_intCast, map_intCast]
        exact Subalgebra.intCast_mem _ n
      | add y z hy hz ihy ihz =>
        rw [show (⟨y + z, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) = ⟨y, hy⟩ + ⟨z, hz⟩
            from rfl, map_add]
        exact add_mem ihy ihz
      | mul y z hy hz ihy ihz =>
        rw [show (⟨y * z, _⟩ : ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) = ⟨y, hy⟩ * ⟨z, hz⟩
            from rfl, map_mul]
        exact mul_mem ihy ihz
    obtain ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj, ι, hι⟩ :=
      bridge (B := ↥(heckeDiamondRing (level N r qv) H S (HR N r qv) 𝒪)) χ μ hker' A hAfg hχA
    refine ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj, Or.inr ⟨ψ₁, ψ₂, ι, ?_, ?_, ?_⟩⟩
    · intro u hu
      rw [hψe u, heH u hu, Units.val_one]
    · intro ℓ hℓ hℓS hℓL
      have h1 : (⟨ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)),
            Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)⟩ : ↥A) +
          (ℓ : ↥A) * ⟨ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)),
            Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ =
          ⟨χ (heckeDiamondRing.T (level N r qv) H S (HR N r qv) 𝒪 ℓ hℓ hℓS hℓL), hχA _⟩ :=
        Subtype.ext (hχT ℓ hℓ hℓS hℓL).symm
      rw [← map_natCast ι ℓ, ← map_mul, ← map_add, h1, hι, hμT]
    · intro u hu
      have h1 : (⟨ψ₁ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)⟩ : ↥A) *
          ⟨ψ₂ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
          ⟨χ (heckeDiamondRing.diamond (level N r qv) H S (HR N r qv) 𝒪 u hu), hχA _⟩ :=
        Subtype.ext ((hψe u).trans (heχ u hu))
      rw [← map_mul, h1, hι, hμD]

end Main

end ClassicalityAsm

end

open IsLocalRing CuspForm.TWLevel

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] 𝒪') :
    ∃ (𝒪₁ : Type) (_ : CommRing 𝒪₁) (_ : IsDomain 𝒪₁) (_ : IsDiscreteValuationRing 𝒪₁)
      (_ : IsAdicComplete (maximalIdeal 𝒪₁) 𝒪₁) (_ : Finite (ResidueField 𝒪₁)) (_ : CharZero 𝒪₁)
      (_ : Algebra 𝒪' 𝒪₁) (_ : Module.Finite 𝒪' 𝒪₁) (_ : IsLocalHom (algebraMap 𝒪' 𝒪₁)),
      Function.Injective (algebraMap 𝒪' 𝒪₁) ∧
      ((∃ (ε : DirichletCharacter ℂ (level N r qv))
          (h : CuspForm (CongruenceSubgroup.Gamma1 (level N r qv)) 2)
          (ι : Algebra.adjoin ℤ ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
              Set.range fun u : (ZMod (level N r qv))ˣ => ε (u : ZMod (level N r qv))) →+* 𝒪₁),
          CuspForm.IsEigenformWith ε h ∧
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H → ε (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ModularFormClass.qCoeff h ℓ, Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ε (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu)))) ∨
       (∃ (ψ₁ ψ₂ : DirichletCharacter ℂ (level N r qv))
          (ι : Algebra.adjoin ℤ
              ((Set.range fun u : (ZMod (level N r qv))ˣ => ψ₁ (u : ZMod (level N r qv))) ∪
                Set.range fun u : (ZMod (level N r qv))ˣ => ψ₂ (u : ZMod (level N r qv))) →+* 𝒪₁),
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H →
            ψ₁ (u : ZMod (level N r qv)) * ψ₂ (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)),
                Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)⟩ +
              (ℓ : 𝒪₁) * ι ⟨ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) :
                  ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ψ₁ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)⟩ *
                ι ⟨ψ₂ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu))))) :=
  ClassicalityAsm.main S N r θ t qv α H hc hdc 𝒪' lam

end S_CuspForm_TWLevel_HeckeRing_exists_isEigenformWith_or_eisenstein_of_algHom
end P2MW
export P2MW.S_CuspForm_TWLevel_HeckeRing_exists_isEigenformWith_or_eisenstein_of_algHom (solution)
