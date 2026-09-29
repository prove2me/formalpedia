-- Prove2me | solution 1 for CuspForm.TWLevel.HeckeRing.isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/92f1fe7b-02f6-5b73-af62-60c56824c79b

import Mathlib
import Definitions.Def_CuspForm_TWLevelHeckeRing
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_exists_squarefree_aeval_heckeTL_eq_zero
import Theorems.Thm_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one"
p2m_attr_erase "simp" "Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open Polynomial

namespace Red111

section GroupTheory

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem Gamma_le_GammaH : CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem isCongruenceSubgroup_GammaH : CongruenceSubgroup.IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
  ⟨M, NeZero.ne _, Gamma_le_GammaH M H⟩

scoped instance GammaH_finiteIndex : (CohCarrier.GammaH M H).FiniteIndex :=
  (isCongruenceSubgroup_GammaH M H).finiteIndex

scoped instance SL2Z_fg : Group.FG SL(2, ℤ) := by
  rw [Group.fg_iff]
  exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

scoped instance GammaH_fg : Group.FG ↥(CohCarrier.GammaH M H) := inferInstance

theorem moduleFinite_H1 (K : Type) [Field K] : Module.Finite K (CohCarrier.H1 M H K) := by
  classical
  obtain ⟨T, hT⟩ := (Group.fg_iff (G := ↥(CohCarrier.GammaH M H))).mp inferInstance |>.imp fun T hT => hT

  haveI : Fintype ↥T := hT.2.fintype
  let e : CohCarrier.H1 M H K →ₗ[K] (↥T → K) :=
    { toFun := fun φ t => φ (Additive.ofMul (t : ↥(CohCarrier.GammaH M H)))
      map_add' := fun φ ψ => rfl
      map_smul' := fun c φ => rfl }
  refine Module.Finite.of_injective e ?_
  intro φ ψ h

  have hmul : (AddMonoidHom.toMultiplicative φ : ↥(CohCarrier.GammaH M H) →* Multiplicative K)
      = AddMonoidHom.toMultiplicative ψ := by
    apply MonoidHom.eq_of_eqOn_dense hT.1
    intro t ht
    have := congrFun h ⟨t, ht⟩
    exact congrArg Multiplicative.ofAdd this
  exact AddMonoidHom.toMultiplicative.injective hmul

end GroupTheory

end Red111
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced.Red111"

namespace Red111

section Coeff

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K]

def jW : CohCarrier.H1 M H 𝒪 →ₗ[𝒪] CohCarrier.H1 M H K where
  toFun φ := (algebraMap 𝒪 K : 𝒪 →+ K).comp φ
  map_add' φ ψ := by ext; simp
  map_smul' r φ := by
    ext γ
    show algebraMap 𝒪 K (r • φ γ) = r • algebraMap 𝒪 K (φ γ)
    rw [smul_eq_mul, map_mul, Algebra.smul_def]

theorem jW_apply (φ : CohCarrier.H1 M H 𝒪) (γ : Additive ↥(CohCarrier.GammaH M H)) :
    jW M H 𝒪 K φ γ = algebraMap 𝒪 K (φ γ) := rfl

theorem jW_injective [IsDomain 𝒪] [IsFractionRing 𝒪 K] : Function.Injective (jW M H 𝒪 K) := by
  intro φ ψ h
  refine AddMonoidHom.ext fun γ => ?_
  exact IsFractionRing.injective 𝒪 K (by rw [← jW_apply, ← jW_apply, h])

theorem heckeTL_jW (ℓ : ℕ) [NeZero ℓ] (φ : CohCarrier.H1 M H 𝒪) :
    CohCarrier.heckeTL M H K ℓ (jW M H 𝒪 K φ) = jW M H 𝒪 K (CohCarrier.heckeTL M H 𝒪 ℓ φ) := by
  rw [CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply]
  exact CohCarrier.heckeT_comp_coeff M H ℓ (algebraMap 𝒪 K : 𝒪 →+ K) φ

theorem diamondL_jW (d : (ZMod M)ˣ) (φ : CohCarrier.H1 M H 𝒪) :
    CohCarrier.diamondL M H K d (jW M H 𝒪 K φ) = jW M H 𝒪 K (CohCarrier.diamondL M H 𝒪 d φ) := rfl

theorem exists_jW_eq_smul [IsDomain 𝒪] [IsFractionRing 𝒪 K] (w : CohCarrier.H1 M H K) :
    ∃ d : 𝒪, d ≠ 0 ∧ ∃ v : CohCarrier.H1 M H 𝒪, jW M H 𝒪 K v = algebraMap 𝒪 K d • w := by
  classical
  obtain ⟨T, hT1, hT2⟩ := (Group.fg_iff (G := ↥(CohCarrier.GammaH M H))).mp inferInstance
  haveI : Fintype ↥T := hT2.fintype
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪)
    (fun t : ↥T => w (Additive.ofMul (t : ↥(CohCarrier.GammaH M H))))
  have hinj : Function.Injective (algebraMap 𝒪 K : 𝒪 →+ K) := IsFractionRing.injective 𝒪 K
  let R : AddSubgroup K := (algebraMap 𝒪 K : 𝒪 →+ K).range
  let w' : Additive ↥(CohCarrier.GammaH M H) →+ K := (b : 𝒪) • w
  have hw' : ∀ γ, w' γ = algebraMap 𝒪 K b * w γ := fun γ => by
    show (b : 𝒪) • w γ = _; rw [Algebra.smul_def]
  have hall : ∀ γ, w' γ ∈ R := by

    suffices h : (⊤ : Subgroup ↥(CohCarrier.GammaH M H)) ≤ (R.comap w').toSubgroup by
      intro γ
      have := h (Subgroup.mem_top (Additive.toMul γ))
      exact this
    rw [← hT1, Subgroup.closure_le]
    intro t ht
    show w' (Additive.ofMul t) ∈ R
    obtain ⟨a, ha⟩ := hb ⟨t, ht⟩
    refine ⟨a, ?_⟩
    rw [hw']
    rw [Algebra.smul_def] at ha
    exact ha
  let e : 𝒪 ≃+ ↥R := AddMonoidHom.ofInjective hinj
  let v : CohCarrier.H1 M H 𝒪 := e.symm.toAddMonoidHom.comp (w'.codRestrict R hall)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, v, ?_⟩
  refine AddMonoidHom.ext fun γ => ?_
  rw [jW_apply]
  show algebraMap 𝒪 K (e.symm (w'.codRestrict R hall γ)) = algebraMap 𝒪 K b • w γ
  have key : ∀ x : ↥R, (algebraMap 𝒪 K : 𝒪 →+ K) (e.symm x) = (x : K) := by
    intro x
    have h1 : ((e (e.symm x) : ↥R) : K) = (x : K) := by rw [AddEquiv.apply_symm_apply]
    rw [AddMonoidHom.ofInjective_apply] at h1
    exact h1
  have := key (w'.codRestrict R hall γ)
  rw [smul_eq_mul, ← hw']
  exact this

theorem ext_of_jW [IsDomain 𝒪] [IsFractionRing 𝒪 K] {X : Type} [AddCommGroup X] [Module K X]
    {F G : CohCarrier.H1 M H K →ₗ[K] X}
    (h : ∀ v : CohCarrier.H1 M H 𝒪, F (jW M H 𝒪 K v) = G (jW M H 𝒪 K v)) : F = G := by
  apply LinearMap.ext
  intro w
  obtain ⟨d, hd, v, hv⟩ := exists_jW_eq_smul M H 𝒪 K w
  have hd' : algebraMap 𝒪 K d ≠ 0 := fun h0 => hd (IsFractionRing.injective 𝒪 K (by rw [h0, map_zero]))
  have := h v
  rw [hv, map_smul, map_smul] at this
  exact smul_right_injective X hd' this

end Coeff
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced.Red111"

end Red111
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced.Red111"

namespace Red111

section TW

open CuspForm.TWLevel

variable (N r : ℕ) [NeZero N] [NeZero r] {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
  (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ)
  (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

theorem op_jW (g : Gen (level N r qv) S t) (φ : Carrier N r qv 𝒪 H) :
    op N r qv S K H g (jW (level N r qv) H 𝒪 K φ) = jW (level N r qv) H 𝒪 K (op N r qv S 𝒪 H g φ) := by
  cases g with
  | T ℓ hℓ hℓS hℓL =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact heckeTL_jW (level N r qv) H 𝒪 K ℓ φ
  | U i => exact heckeTL_jW (level N r qv) H 𝒪 K (qv i) φ

theorem opComm_K (hc : OpComm N r qv S 𝒪 H) : OpComm N r qv S K H := by
  intro g h
  apply ext_of_jW (level N r qv) H 𝒪 K
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, op_jW, op_jW, op_jW, op_jW, ← Module.End.mul_apply,
    hc g h, Module.End.mul_apply]

theorem diaComm_K (hdc : DiaComm N r qv S 𝒪 H) : DiaComm N r qv S K H := by
  intro u g
  apply ext_of_jW (level N r qv) H 𝒪 K
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, op_jW, diamondL_jW, diamondL_jW, op_jW,
    ← Module.End.mul_apply, hdc u g, Module.End.mul_apply]

def gensK : Set (Module.End K (Carrier N r qv K H)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      T = op N r qv S K H (Gen.T ℓ hℓ hℓS hℓL)} ∪
  {D | ∃ u ∈ HR N r qv, D = CohCarrier.diamondL (level N r qv) H K u}

theorem gensK_comm (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H) :
    ∀ a ∈ gensK N r qv S H K, ∀ b ∈ gensK N r qv S H K, a * b = b * a := by
  have hcK := opComm_K N r qv S 𝒪 H K hc
  have hdcK := diaComm_K N r qv S 𝒪 H K hdc
  rintro a (⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩) b (⟨ℓ', hℓ', hℓS', hℓL', rfl⟩ | ⟨v, hv, rfl⟩)
  · exact hcK _ _
  · exact (hdcK v _).symm
  · exact hdcK u _
  · exact CohCarrier.diamondL_comm (level N r qv) H K u v

theorem op_comm_of_mem_adjoin (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    {x : Module.End K (Carrier N r qv K H)} (hx : x ∈ Algebra.adjoin K (gensK N r qv S H K))
    (g : Gen (level N r qv) S t) :
    x * op N r qv S K H g = op N r qv S K H g * x := by
  have hcK := opComm_K N r qv S 𝒪 H K hc
  have hdcK := diaComm_K N r qv S 𝒪 H K hdc
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩
    · exact hcK _ _
    · exact hdcK u g
  | algebraMap c => exact Algebra.commutes c _
  | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
  | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]

theorem isSemisimple_of_pow_eq_one' {F : Type} [Field F] [CharZero F] {Y : Type} [AddCommGroup Y] [Module F Y]
    (f : Module.End F Y) {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) : f.IsSemisimple := by
  have hsq : Squarefree (X ^ n - C (1 : F) : F[X]) :=
    (separable_X_pow_sub_C (1 : F) (by exact_mod_cast hn.ne') one_ne_zero).squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq
  rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hf, sub_self]

theorem gensK_isSemisimple [CharZero K] : ∀ x ∈ gensK N r qv S H K, Module.End.IsSemisimple x := by
  rintro x (⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩)
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨p, hp, hp0⟩ := CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero (level N r qv) H hℓ hℓL K
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp hp0
  · let Dh : (ZMod (level N r qv))ˣ →* Module.End K (Carrier N r qv K H) :=
      { toFun := CohCarrier.diamondL (level N r qv) H K
        map_one' := CohCarrier.diamondL_one (level N r qv) H K
        map_mul' := CohCarrier.diamondL_mul (level N r qv) H K }
    have : CohCarrier.diamondL (level N r qv) H K u ^ orderOf u = 1 := by
      rw [show CohCarrier.diamondL (level N r qv) H K u = Dh u from rfl, ← map_pow, pow_orderOf_eq_one, map_one]
    exact isSemisimple_of_pow_eq_one' _ (orderOf_pos u) this

variable [IsLocalRing 𝒪]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪)

@[reducible] noncomputable def dataK (hc : OpComm N r qv S 𝒪 H) :
    CohCarrier.HeckeData K (Carrier N r qv K H) K where
  Gen := (heckeData N r qv S 𝒪 H θ α hc).Gen
  op := op N r qv S K H
  comm := opComm_K N r qv S 𝒪 H K hc
  θbar := fun _ => 0

noncomputable def sK (hc : OpComm N r qv S 𝒪 H) :
    (heckeData N r qv S 𝒪 H θ α hc).FreeAlg →+* Module.End K (Carrier N r qv K H) :=
  ((dataK N r qv S 𝒪 H K θ α hc).opAlgHom.toRingHom).comp (MvPolynomial.map (algebraMap 𝒪 K))

theorem sK_apply (hc : OpComm N r qv S 𝒪 H) (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) :
    sK N r qv S 𝒪 H K θ α hc s = (dataK N r qv S 𝒪 H K θ α hc).opAlgHom (MvPolynomial.map (algebraMap 𝒪 K) s) := rfl

theorem sK_X (hc : OpComm N r qv S 𝒪 H) (g : (heckeData N r qv S 𝒪 H θ α hc).Gen) :
    sK N r qv S 𝒪 H K θ α hc (MvPolynomial.X g) = op N r qv S K H g := by
  rw [sK_apply, MvPolynomial.map_X, CohCarrier.HeckeData.opAlgHom_X]

theorem sK_C (hc : OpComm N r qv S 𝒪 H) (a : 𝒪) :
    sK N r qv S 𝒪 H K θ α hc (MvPolynomial.C a) = algebraMap K (Module.End K (Carrier N r qv K H)) (algebraMap 𝒪 K a) := by
  rw [sK_apply, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]

theorem sK_comm (hc : OpComm N r qv S 𝒪 H) (p q : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) :
    sK N r qv S 𝒪 H K θ α hc p * sK N r qv S 𝒪 H K θ α hc q = sK N r qv S 𝒪 H K θ α hc q * sK N r qv S 𝒪 H K θ α hc p := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem jW_smul (hc : OpComm N r qv S 𝒪 H) (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) (v : Carrier N r qv 𝒪 H) :
    jW (level N r qv) H 𝒪 K (s • v) = sK N r qv S 𝒪 H K θ α hc s (jW (level N r qv) H 𝒪 K v) := by
  revert v
  induction s using MvPolynomial.induction_on with
  | C a =>
    intro v
    rw [sK_C, Module.algebraMap_end_apply, algebraMap_smul, ← MvPolynomial.algebraMap_eq,
      CohCarrier.HeckeData.algebraMap_freeAlg_smul, LinearMap.map_smul_of_tower]
  | add p q hp hq =>
    intro v
    rw [add_smul, LinearMap.map_add, hp, hq, map_add, LinearMap.add_apply]
  | mul_X p g hp =>
    intro v
    have hX : (MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • v = op N r qv S 𝒪 H g v := by
      show (heckeData N r qv S 𝒪 H θ α hc).opAlgHom (MvPolynomial.X g) v = _
      rw [CohCarrier.HeckeData.opAlgHom_X]
      rfl
    rw [mul_smul, map_mul, Module.End.mul_apply, sK_X, hX, hp (op N r qv S 𝒪 H g v), op_jW]

theorem sK_comm_of_mem_adjoin (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    {x : Module.End K (Carrier N r qv K H)} (hx : x ∈ Algebra.adjoin K (gensK N r qv S H K))
    (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) :
    x * sK N r qv S 𝒪 H K θ α hc s = sK N r qv S 𝒪 H K θ α hc s * x := by
  induction s using MvPolynomial.induction_on with
  | C a => rw [sK_C]; exact (Algebra.commutes _ _).symm
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | mul_X p g hp =>
    rw [map_mul, sK_X, ← mul_assoc, hp, mul_assoc, op_comm_of_mem_adjoin N r qv S 𝒪 H K hc hdc hx g, ← mul_assoc]

end TW
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced.Red111"

end Red111
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced.Red111"

namespace Red111

section Main

open CuspForm.TWLevel

variable (N r : ℕ) [NeZero N] [NeZero r] {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
  (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ)
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪)
  (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
  (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

def Tracked (f : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) : Prop :=
  ∃ (b : Module.End 𝒪 (Carrier N r qv 𝒪 H)) (c : Module.End K (Carrier N r qv K H)),
    c ∈ Algebra.adjoin K (gensK N r qv S H K) ∧
    (∀ v, f ((heckeData N r qv S 𝒪 H θ α hc).toML v) = (heckeData N r qv S 𝒪 H θ α hc).toML (b v)) ∧
    (∀ v, c (jW (level N r qv) H 𝒪 K v) = jW (level N r qv) H 𝒪 K (b v)) ∧
    (∀ (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) (m : ML N r qv S 𝒪 H θ α hc), f (s • m) = s • f m)

theorem tracked_of_mem (f : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc))
    (hx : f ∈ Algebra.adjoin 𝒪 (heckeRingGens N r qv S 𝒪 H θ α hc hdc)) :
    Tracked N r qv S 𝒪 H θ α hc K f := by
  induction hx using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩
    · refine ⟨op N r qv S 𝒪 H (Gen.T ℓ hℓ hℓS hℓL), op N r qv S K H (Gen.T ℓ hℓ hℓS hℓL),
        Algebra.subset_adjoin (Or.inl ⟨ℓ, hℓ, hℓS, hℓL, rfl⟩), ?_, ?_, ?_⟩
      · intro v
        rw [opML_apply, X_smul_toML]
      · intro v
        exact op_jW N r qv S 𝒪 H K _ v
      · intro s m
        rw [opML_apply, opML_apply, smul_smul, smul_smul, mul_comm]
    · refine ⟨CohCarrier.diamondL (level N r qv) H 𝒪 u, CohCarrier.diamondL (level N r qv) H K u,
        Algebra.subset_adjoin (Or.inr ⟨u, hu, rfl⟩), ?_, ?_, ?_⟩
      · intro v
        exact diaML_toML N r qv S 𝒪 H θ α hc hdc u v
      · intro v
        exact diamondL_jW (level N r qv) H 𝒪 K u v
      · intro s m
        exact diaML_smul N r qv S 𝒪 H θ α hc hdc u s m
  | algebraMap a =>
    refine ⟨algebraMap 𝒪 _ a, algebraMap K _ (algebraMap 𝒪 K a), Subalgebra.algebraMap_mem _ _, ?_, ?_, ?_⟩
    · intro v
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smul_of_tower]
    · intro v
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, algebraMap_smul, LinearMap.map_smul_of_tower]
    · intro s m
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, smul_comm]
  | add f g _ _ hf hg =>
    obtain ⟨b, c, hcm, h1, h2, h3⟩ := hf
    obtain ⟨b', c', hcm', h1', h2', h3'⟩ := hg
    refine ⟨b + b', c + c', add_mem hcm hcm', ?_, ?_, ?_⟩
    · intro v; rw [LinearMap.add_apply, h1, h1', LinearMap.add_apply, map_add]
    · intro v; rw [LinearMap.add_apply, h2, h2', LinearMap.add_apply, map_add]
    · intro s m; rw [LinearMap.add_apply, LinearMap.add_apply, h3, h3', smul_add]
  | mul f g _ _ hf hg =>
    obtain ⟨b, c, hcm, h1, h2, h3⟩ := hf
    obtain ⟨b', c', hcm', h1', h2', h3'⟩ := hg
    refine ⟨b * b', c * c', mul_mem hcm hcm', ?_, ?_, ?_⟩
    · intro v; rw [Module.End.mul_apply, h1', h1, Module.End.mul_apply]
    · intro v; rw [Module.End.mul_apply, h2', h2, Module.End.mul_apply]
    · intro s m; rw [Module.End.mul_apply, Module.End.mul_apply, h3', h3]

theorem tracked_act (x : HeckeRing N r qv S 𝒪 H θ α hc hdc) :
    Tracked N r qv S 𝒪 H θ α hc K (HeckeRing.act N r qv S 𝒪 H θ α hc hdc x) :=
  tracked_of_mem N r qv S 𝒪 H θ α hc hdc K _ (by
    have hx := x.2
    unfold heckeSubalgebra at hx
    exact hx)

theorem tracked_pow {f : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)} {b : Module.End 𝒪 (Carrier N r qv 𝒪 H)}
    {c : Module.End K (Carrier N r qv K H)}
    (h1 : ∀ v, f ((heckeData N r qv S 𝒪 H θ α hc).toML v) = (heckeData N r qv S 𝒪 H θ α hc).toML (b v))
    (h2 : ∀ v, c (jW (level N r qv) H 𝒪 K v) = jW (level N r qv) H 𝒪 K (b v)) (n : ℕ) :
    (∀ v, (f ^ n) ((heckeData N r qv S 𝒪 H θ α hc).toML v) = (heckeData N r qv S 𝒪 H θ α hc).toML ((b ^ n) v)) ∧
    (∀ v, (c ^ n) (jW (level N r qv) H 𝒪 K v) = jW (level N r qv) H 𝒪 K ((b ^ n) v)) := by
  induction n with
  | zero =>
    exact ⟨fun v => by rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply],
      fun v => by rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]⟩
  | succ n ih =>
    refine ⟨fun v => ?_, fun v => ?_⟩
    · rw [pow_succ, Module.End.mul_apply, h1, ih.1, pow_succ, Module.End.mul_apply]
    · rw [pow_succ, Module.End.mul_apply, h2, ih.2, pow_succ, Module.End.mul_apply]

variable [CharZero 𝒪]

include hdc in

theorem eq_zero_of_tracked_of_isNilpotent (f : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc))
    (hf : Tracked N r qv S 𝒪 H θ α hc K f) (hn : IsNilpotent f) : f = 0 := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  haveI : Module.Finite K (Carrier N r qv K H) := moduleFinite_H1 (level N r qv) H K
  haveI hloc : IsLocalizedModule (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl (heckeData N r qv S 𝒪 H θ α hc).toML := by
    show IsLocalizedModule _ (LocalizedModule.mkLinearMap _ _)
    infer_instance
  obtain ⟨b, c, hcm, h1, h2, h3⟩ := hf
  obtain ⟨n, hfn⟩ := hn
  have hpow := tracked_pow N r qv S 𝒪 H θ α hc K h1 h2 n

  have hkill : ∀ v : Carrier N r qv 𝒪 H, ∃ s : (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl, (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • (b ^ n) v = 0 := by
    intro v
    have : (heckeData N r qv S 𝒪 H θ α hc).toML ((b ^ n) v) = 0 := by rw [← hpow.1, hfn, LinearMap.zero_apply]
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl (heckeData N r qv S 𝒪 H θ α hc).toML).mp this
    exact ⟨s, hs⟩

  let Wbad : Submodule K (Carrier N r qv K H) :=
    { carrier := {w | ∃ s : (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl, sK N r qv S 𝒪 H K θ α hc (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) w = 0}
      zero_mem' := ⟨1, by rw [map_zero]⟩
      add_mem' := by
        rintro w₁ w₂ ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
        refine ⟨s₁ * s₂, ?_⟩
        show sK N r qv S 𝒪 H K θ α hc ((s₁ : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) * s₂) (w₁ + w₂) = 0
        rw [map_mul, map_add, Module.End.mul_apply, Module.End.mul_apply, hs₂, map_zero, add_zero,
          ← Module.End.mul_apply, sK_comm, Module.End.mul_apply, hs₁, map_zero]
      smul_mem' := by
        rintro a w ⟨s, hs⟩
        exact ⟨s, by rw [map_smul, hs, smul_zero]⟩ }
  have hWbad_mem : ∀ {w}, w ∈ Wbad ↔ ∃ s : (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl, sK N r qv S 𝒪 H K θ α hc (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) w = 0 :=
    fun {w} => Iff.rfl

  have hcn : ∀ w, (c ^ n) w ∈ Wbad := by
    intro w
    obtain ⟨d, hd, v, hv⟩ := exists_jW_eq_smul (level N r qv) H 𝒪 K w
    have hd' : algebraMap 𝒪 K d ≠ 0 := fun h0 => hd (IsFractionRing.injective 𝒪 K (by rw [h0, map_zero]))
    have hv' : (c ^ n) (jW (level N r qv) H 𝒪 K v) ∈ Wbad := by
      obtain ⟨s, hs⟩ := hkill v
      refine (hWbad_mem).mpr ⟨s, ?_⟩
      rw [hpow.2, ← jW_smul N r qv S 𝒪 H K θ α hc, hs, map_zero]
    rw [hv, map_smul] at hv'
    have := Wbad.smul_mem (algebraMap 𝒪 K d)⁻¹ hv'
    rwa [smul_smul, inv_mul_cancel₀ hd', one_smul] at this

  have hinv : Wbad ∈ Module.End.invtSubmodule c := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    rintro w ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [← Module.End.mul_apply, ← sK_comm_of_mem_adjoin N r qv S 𝒪 H K θ α hc hdc hcm, Module.End.mul_apply, hs,
      map_zero]

  have hss : c.IsSemisimple :=
    (Module.End.forall_isSemisimple_and_isReduced_adjoin_of_commute (gensK_comm N r qv S 𝒪 H K hc hdc)
      (gensK_isSemisimple N r qv S H K)).1 c hcm
  obtain ⟨q, hq, hcompl⟩ := Module.End.isSemisimple_iff.mp hss Wbad hinv
  have hqpow : ∀ (k : ℕ) (u : Carrier N r qv K H), u ∈ q → (c ^ k) u ∈ q := by
    intro k
    induction k with
    | zero => intro u hu; rwa [pow_zero, Module.End.one_apply]
    | succ k ih => intro u hu; rw [pow_succ', Module.End.mul_apply]; exact hq (ih u hu)
  have hcq : ∀ u ∈ q, c u = 0 := by
    have hres : IsNilpotent (LinearMap.restrict c hq) := by
      refine ⟨n, LinearMap.ext fun u => Subtype.ext ?_⟩
      have hmem : (c ^ n) (u : Carrier N r qv K H) ∈ Wbad ⊓ q := ⟨hcn u, hqpow n u u.2⟩
      rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
      rw [Module.End.pow_restrict n, LinearMap.restrict_apply]
      exact hmem
    have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hres (hss.restrict hq)
    intro u hu
    have := congrArg (fun F => ((F ⟨u, hu⟩ : ↥q) : Carrier N r qv K H)) h0
    simpa [LinearMap.restrict_apply] using this

  have hcW : ∀ w, c w ∈ Wbad := by
    intro w
    have hw : w ∈ Wbad ⊔ q := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hcq z hz, add_zero]
    exact hinv hy

  have hfv : ∀ v, f ((heckeData N r qv S 𝒪 H θ α hc).toML v) = 0 := by
    intro v
    obtain ⟨s, hs⟩ := (hWbad_mem).mp (hcW (jW (level N r qv) H 𝒪 K v))
    rw [h2, ← jW_smul N r qv S 𝒪 H K θ α hc] at hs
    have hsv : (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • b v = 0 := jW_injective (level N r qv) H 𝒪 K (by rw [hs, map_zero])
    rw [h1]
    exact (IsLocalizedModule.eq_zero_iff (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl (heckeData N r qv S 𝒪 H θ α hc).toML).mpr ⟨s, hsv⟩

  apply LinearMap.ext
  intro m
  induction m using LocalizedModule.induction_on with
  | h v s =>
    have hu := IsLocalizedModule.map_units (heckeData N r qv S 𝒪 H θ α hc).toML s
    have key : (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • f (LocalizedModule.mk v s) = 0 := by
      rw [← h3, LocalizedModule.smul'_mk]
      have : LocalizedModule.mk ((s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • v) s = (heckeData N r qv S 𝒪 H θ α hc).toML v := by
        rw [show (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • v = s • v from rfl, LocalizedModule.mk_cancel]; rfl
      rw [this]
      exact hfv v
    rw [LinearMap.zero_apply]
    have : (algebraMap (heckeData N r qv S 𝒪 H θ α hc).FreeAlg (Module.End (heckeData N r qv S 𝒪 H θ α hc).FreeAlg (heckeData N r qv S 𝒪 H θ α hc).ML) (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg)) (f (LocalizedModule.mk v s)) = 0 := by
      rw [Module.algebraMap_end_apply]; exact key
    exact ((Module.End.isUnit_iff _).mp hu).1 (by rw [this, map_zero])

theorem isReduced_heckeRing : IsReduced (HeckeRing N r qv S 𝒪 H θ α hc hdc) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  apply HeckeRing.act_injective N r qv S 𝒪 H θ α hc hdc
  rw [map_zero]
  apply eq_zero_of_tracked_of_isNilpotent N r qv S 𝒪 H θ α hc hdc (FractionRing 𝒪)
    (HeckeRing.act N r qv S 𝒪 H θ α hc hdc x) (tracked_act N r qv S 𝒪 H θ α hc hdc (FractionRing 𝒪) x)
  exact ⟨n, by rw [← map_pow, hn, map_zero]⟩

end Main
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced.Red111"

end Red111
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced.Red111"

open IsLocalRing CuspForm.TWLevel in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    (N r : ℕ) [NeZero N] [NeZero r] {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
    (S : Set ℕ) (H : Subgroup (ZMod (level N r qv))ˣ)
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪) (α : Fin t → ResidueField 𝒪)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H) :
    IsReduced (HeckeRing N r qv S 𝒪 H θ α hc hdc) :=
  Red111.isReduced_heckeRing N r qv S 𝒪 H θ α hc hdc

end S_CuspForm_TWLevel_HeckeRing_isReduced
end P2MW
export P2MW.S_CuspForm_TWLevel_HeckeRing_isReduced (solution)
