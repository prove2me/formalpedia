-- Prove2me | solution 1 for CohCarrier.exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/487a7d01-a443-5ba4-9b49-0e756cc3bdd9

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
import Theorems.Thm_CohCarrier_heckeT_mem_parabolicHoms
import Theorems.Thm_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
import Theorems.Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_Module_End_exists_common_eigenvector_of_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex CuspForm.GammaH_finiteIndex CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z"
p2m_attr_erase "instance" "FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CohCarrier.jConjGammaH_jConjGammaH"
p2m_attr_erase "simp" "CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups
open CongruenceSubgroup

namespace RSplit

section General

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem Gamma_le_GammaH : Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  have hA0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact h10
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext; rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11
  rw [this]; exact one_mem H

scoped instance GammaH_finiteIndex : (CohCarrier.GammaH M H).FiniteIndex :=
  IsCongruenceSubgroup.finiteIndex ⟨M, NeZero.ne _, Gamma_le_GammaH M H⟩

scoped instance SL2Z_fg : Group.FG SL(2, ℤ) := by
  rw [Group.fg_iff]
  exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

scoped instance GammaH_fg : Group.FG ↥(CohCarrier.GammaH M H) := inferInstance

scoped instance moduleFinite_H1 : Module.Finite ℂ (CohCarrier.H1 M H ℂ) := by
  classical
  obtain ⟨T, hT1, hT2⟩ := (Group.fg_iff (G := ↥(CohCarrier.GammaH M H))).mp inferInstance
  haveI : Fintype ↥T := hT2.fintype
  let e : CohCarrier.H1 M H ℂ →ₗ[ℂ] (↥T → ℂ) :=
    { toFun := fun φ t => φ (Additive.ofMul (t : ↥(CohCarrier.GammaH M H)))
      map_add' := fun φ ψ => rfl
      map_smul' := fun c φ => rfl }
  refine Module.Finite.of_injective e ?_
  intro φ ψ h
  have hmul : (AddMonoidHom.toMultiplicative φ : ↥(CohCarrier.GammaH M H) →* Multiplicative ℂ)
      = AddMonoidHom.toMultiplicative ψ := by
    apply MonoidHom.eq_of_eqOn_dense hT1
    intro t ht
    exact congrArg Multiplicative.ofAdd (congrFun h ⟨t, ht⟩)
  exact AddMonoidHom.toMultiplicative.injective hmul

theorem mem_par_iff (φ : CohCarrier.H1 M H ℂ) :
    φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ ↔
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℂ := Iff.rfl

theorem heckeTL_mem_par (ℓ : ℕ) [NeZero ℓ] {φ : CohCarrier.H1 M H ℂ}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) :
    CohCarrier.heckeTL M H ℂ ℓ φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ :=
  CohCarrier.heckeT_mem_parabolicHoms M H ℂ ℓ φ hφ

theorem diamondRaw_mem_par (σ : Gamma0 M) {φ : CohCarrier.H1 M H ℂ}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) :
    CohCarrier.diamondRaw M H ℂ σ φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by
  intro γ hγ
  show φ (Additive.ofMul (CohCarrier.conjHom M H σ γ)) = 0
  apply hφ
  have : ((CohCarrier.conjHom M H σ γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
      (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ := rfl
  rw [this, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle, Matrix.SpecialLinearGroup.coe_inv, ← Matrix.SpecialLinearGroup.coe_inv,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  exact hγ

theorem diamondL_mem_par (u : (ZMod M)ˣ) {φ : CohCarrier.H1 M H ℂ}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) :
    CohCarrier.diamondL M H ℂ u φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ :=
  diamondRaw_mem_par M H _ hφ

theorem diamondRaw_diamondRaw (σ τ : Gamma0 M) (φ : CohCarrier.H1 M H ℂ) :
    CohCarrier.diamondRaw M H ℂ σ (CohCarrier.diamondRaw M H ℂ τ φ) = CohCarrier.diamondRaw M H ℂ (τ * σ) φ := by
  refine AddMonoidHom.ext fun γ => ?_
  show φ (Additive.ofMul (CohCarrier.conjHom M H τ (CohCarrier.conjHom M H σ (Additive.toMul γ)))) =
    φ (Additive.ofMul (CohCarrier.conjHom M H (τ * σ) (Additive.toMul γ)))
  congr 2
  apply Subtype.ext
  simp only [CohCarrier.conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
  group

theorem diamondL_mul (u v : (ZMod M)ˣ) :
    CohCarrier.diamondL M H ℂ (u * v) = CohCarrier.diamondL M H ℂ u * CohCarrier.diamondL M H ℂ v := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective M u
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective M v
  apply LinearMap.ext
  intro φ
  rw [Module.End.mul_apply, CohCarrier.diamondL_eq_diamondRaw M H ℂ v τ hτ,
    CohCarrier.diamondL_eq_diamondRaw M H ℂ u σ hσ, diamondRaw_diamondRaw,
    CohCarrier.diamondL_eq_diamondRaw M H ℂ (u * v) (τ * σ) (by rw [map_mul, hσ, hτ, mul_comm])]

theorem diamondL_one : CohCarrier.diamondL M H ℂ 1 = 1 := by
  apply LinearMap.ext
  intro φ
  rw [CohCarrier.diamondL_eq_diamondRaw M H ℂ 1 1 (map_one _)]
  refine AddMonoidHom.ext fun γ => ?_
  show φ (Additive.ofMul (CohCarrier.conjHom M H 1 (Additive.toMul γ))) = φ γ
  congr 1
  have : CohCarrier.conjHom M H 1 (Additive.toMul γ) = Additive.toMul γ := Subtype.ext (by simp [CohCarrier.conjHom])
  rw [this]
  rfl

theorem diamondL_comm (u v : (ZMod M)ˣ) :
    CohCarrier.diamondL M H ℂ u * CohCarrier.diamondL M H ℂ v = CohCarrier.diamondL M H ℂ v * CohCarrier.diamondL M H ℂ u := by
  rw [← diamondL_mul, ← diamondL_mul, mul_comm]

theorem exists_lift_dvd (ℓ : ℕ) [NeZero ℓ] (u : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, CohCarrier.gamma0Units M σ = u ∧ ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 := by
  haveI : NeZero (ℓ * M) := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne M)⟩
  obtain ⟨u', hu'⟩ := ZMod.unitsMap_surjective (dvd_mul_left M ℓ) u
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective (ℓ * M) u'
  have hdvd : ((ℓ * M : ℕ) : ℤ) ∣ (τ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma0_mem (N := ℓ * M) (A := τ)).mp τ.2)
  have hτ0 : ((τ : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_left _ _) hdvd
  refine ⟨⟨τ, hτ0⟩, ?_, ?_⟩
  · apply Units.ext
    rw [CohCarrier.val_gamma0Units, ← hu', ZMod.unitsMap_def, Units.coe_map, ← hτ, CohCarrier.val_gamma0Units]
    show (((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ZMod.castHom (dvd_mul_left M ℓ) (ZMod M) (((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (ℓ * M))
    rw [map_intCast]
  · exact hdvd

theorem heckeTL_diamondL_comm (ℓ : ℕ) [NeZero ℓ] (u : (ZMod M)ˣ) (φ : CohCarrier.H1 M H ℂ) :
    CohCarrier.heckeTL M H ℂ ℓ (CohCarrier.diamondL M H ℂ u φ) =
      CohCarrier.diamondL M H ℂ u (CohCarrier.heckeTL M H ℂ ℓ φ) := by
  obtain ⟨σ, hσ, hdvd⟩ := exists_lift_dvd M ℓ u
  rw [CohCarrier.diamondL_eq_diamondRaw M H ℂ u σ hσ, CohCarrier.diamondL_eq_diamondRaw M H ℂ u σ hσ,
    CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply]
  exact CohCarrier.heckeT_diamondRaw_comm M H ℓ σ hdvd φ

theorem heckeTL_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (φ : CohCarrier.H1 M H ℂ) :
    CohCarrier.heckeTL M H ℂ ℓ (CohCarrier.heckeTL M H ℂ ℓ' φ) =
      CohCarrier.heckeTL M H ℂ ℓ' (CohCarrier.heckeTL M H ℂ ℓ φ) := by
  by_cases h : ℓ = ℓ'
  · subst h; rfl
  · rw [CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply]
    exact CohCarrier.heckeT_comm_of_prime M H ℓ ℓ' hℓ ((Nat.coprime_primes hℓ hℓ').mpr h) φ

theorem qCoeff_zero_fun (n : ℕ) : ModularFormClass.qCoeff (0 : UpperHalfPlane → ℂ) n = 0 := by
  unfold ModularFormClass.qCoeff
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

end General

end RSplit
p2m_reactivate "P2MW.S_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL.RSplit"

namespace RSplit

section Eigen

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

abbrev Idx (M : ℕ) : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ M} ⊕ (ZMod M)ˣ

noncomputable def fam : Idx M → Module.End ℂ (CohCarrier.H1 M H ℂ)
  | Sum.inl p => haveI : NeZero p.1 := ⟨p.2.1.ne_zero⟩; CohCarrier.heckeTL M H ℂ p.1
  | Sum.inr u => CohCarrier.diamondL M H ℂ u

theorem fam_comm (i j : Idx M) : fam M H i * fam M H j = fam M H j * fam M H i := by
  apply LinearMap.ext; intro φ
  rcases i with p | u <;> rcases j with q | v
  · haveI : NeZero p.1 := ⟨p.2.1.ne_zero⟩; haveI : NeZero q.1 := ⟨q.2.1.ne_zero⟩
    exact heckeTL_comm M H p.2.1 q.2.1 φ
  · haveI : NeZero p.1 := ⟨p.2.1.ne_zero⟩
    exact heckeTL_diamondL_comm M H p.1 v φ
  · haveI : NeZero q.1 := ⟨q.2.1.ne_zero⟩
    exact (heckeTL_diamondL_comm M H q.1 u φ).symm
  · show CohCarrier.diamondL M H ℂ u (CohCarrier.diamondL M H ℂ v φ) = CohCarrier.diamondL M H ℂ v (CohCarrier.diamondL M H ℂ u φ)
    rw [← Module.End.mul_apply, diamondL_comm, Module.End.mul_apply]

theorem eq_zero_of_mem_par_of_heckeTL_eq {ℓ' : ℕ} [NeZero ℓ'] (hℓ' : ℓ'.Prime) (hℓ'M : ¬ ℓ' ∣ M)
    (φ : CohCarrier.H1 M H ℂ) (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)
    (heig : CohCarrier.heckeTL M H ℂ ℓ' φ = ((ℓ' : ℂ) + 1) • φ) : φ = 0 := by
  classical
  by_contra hφ0

  set c : ℂ := (ℓ' : ℂ) + 1 with hc
  let par := ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ
  let P : Submodule ℂ (CohCarrier.H1 M H ℂ) :=
    par ⊓ LinearMap.ker (CohCarrier.heckeTL M H ℂ ℓ' - c • (1 : Module.End ℂ (CohCarrier.H1 M H ℂ)))
  have hmemP : ∀ {ψ}, ψ ∈ P ↔ ψ ∈ par ∧ CohCarrier.heckeTL M H ℂ ℓ' ψ = c • ψ := by
    intro ψ
    simp only [P, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hφP : φ ∈ P := hmemP.mpr ⟨hφ, heig⟩

  have hstab : ∀ (i : Idx M) (ψ : CohCarrier.H1 M H ℂ), ψ ∈ P → fam M H i ψ ∈ P := by
    intro i ψ hψ
    obtain ⟨hψ1, hψ2⟩ := hmemP.mp hψ
    refine hmemP.mpr ⟨?_, ?_⟩
    · rcases i with p | u
      · haveI : NeZero p.1 := ⟨p.2.1.ne_zero⟩
        exact heckeTL_mem_par M H p.1 hψ1
      · exact diamondL_mem_par M H u hψ1
    · have hcomm : fam M H i * CohCarrier.heckeTL M H ℂ ℓ' = CohCarrier.heckeTL M H ℂ ℓ' * fam M H i := by
        have := fam_comm M H i (Sum.inl ⟨ℓ', hℓ', hℓ'M⟩)
        exact this
      have := congrArg (fun F : Module.End ℂ (CohCarrier.H1 M H ℂ) => F ψ) hcomm
      simp only [Module.End.mul_apply] at this
      rw [← this, hψ2, map_smul]

  haveI : Nontrivial ↥P := ⟨⟨⟨φ, hφP⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  let famP : Idx M → Module.End ℂ ↥P := fun i => (fam M H i).restrict (hstab i)
  have hcommP : ∀ i j, Commute (famP i) (famP j) := by
    intro i j
    apply LinearMap.ext; intro ψ; apply Subtype.ext
    show fam M H i (fam M H j ψ) = fam M H j (fam M H i ψ)
    rw [← Module.End.mul_apply, fam_comm, Module.End.mul_apply]
  obtain ⟨χ, v, hv0, hv⟩ := Module.End.exists_common_eigenvector_of_commute famP hcommP
  have hvv : ∀ i, fam M H i (v : CohCarrier.H1 M H ℂ) = χ i • (v : CohCarrier.H1 M H ℂ) := fun i => by
    have := congrArg Subtype.val (hv i); simpa [famP, LinearMap.restrict_apply] using this
  have hv0' : (v : CohCarrier.H1 M H ℂ) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨hvpar, hveig⟩ := hmemP.mp v.2

  let a : ℕ → ℂ := fun p => if h : p.Prime ∧ ¬ p ∣ M then χ (Sum.inl ⟨p, h⟩) else 0
  have hχmul : ∀ u w : (ZMod M)ˣ, χ (Sum.inr (u * w)) = χ (Sum.inr u) * χ (Sum.inr w) := by
    intro u w
    have h1 := hvv (Sum.inr (u * w))
    have h2 : fam M H (Sum.inr (u * w)) (v : CohCarrier.H1 M H ℂ) = (χ (Sum.inr u) * χ (Sum.inr w)) • (v : CohCarrier.H1 M H ℂ) := by
      show CohCarrier.diamondL M H ℂ (u * w) v = _
      rw [diamondL_mul, Module.End.mul_apply]
      have hw := hvv (Sum.inr w); have hu := hvv (Sum.inr u)
      simp only [fam] at hw hu
      rw [hw, map_smul, hu, smul_smul, mul_comm]
    rw [h1] at h2
    exact smul_left_injective ℂ hv0' h2
  have hχone : χ (Sum.inr 1) = 1 := by
    have h1 := hvv (Sum.inr 1)
    have h2 : fam M H (Sum.inr 1) (v : CohCarrier.H1 M H ℂ) = (1 : ℂ) • (v : CohCarrier.H1 M H ℂ) := by
      show CohCarrier.diamondL M H ℂ 1 v = _
      rw [diamondL_one, Module.End.one_apply, one_smul]
    rw [h1] at h2
    exact smul_left_injective ℂ hv0' h2
  have hχunit : ∀ u, IsUnit (χ (Sum.inr u)) := fun u =>
    IsUnit.mk0 _ (left_ne_zero_of_mul_eq_one (by rw [← hχmul, mul_inv_cancel, hχone] : χ (Sum.inr u) * χ (Sum.inr u⁻¹) = 1))
  let e : (ZMod M)ˣ →* ℂˣ :=
    { toFun := fun u => (hχunit u).unit
      map_one' := by apply Units.ext; simp [hχone]
      map_mul' := fun u w => by apply Units.ext; simp [hχmul] }
  have he : ∀ u, (e u : ℂ) = χ (Sum.inr u) := fun u => rfl

  obtain ⟨ε, h, hEig, -, hq⟩ :=
    CohCarrier.exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul M H ∅ (v : CohCarrier.H1 M H ℂ)
      hvpar hv0' a e
      (fun p hp _ hpM => by
        have := hvv (Sum.inl ⟨p, hp, hpM⟩)
        simp only [fam, CohCarrier.heckeTL_apply] at this
        simp only [a, dif_pos (And.intro hp hpM)]
        exact this)
      (fun u => by rw [he]; exact hvv (Sum.inr u))

  have haℓ : a ℓ' = c := by
    have h1 := hvv (Sum.inl ⟨ℓ', hℓ', hℓ'M⟩)
    simp only [fam] at h1
    rw [hveig] at h1
    have : a ℓ' = χ (Sum.inl ⟨ℓ', hℓ', hℓ'M⟩) := by simp only [a, dif_pos (And.intro hℓ' hℓ'M)]
    rw [this]
    exact (smul_left_injective ℂ hv0' h1).symm
  have hqℓ : ModularFormClass.qCoeff h ℓ' = c := by rw [hq ℓ' hℓ' (Set.notMem_empty _) hℓ'M, haℓ]

  have hh0 : h ≠ 0 := by
    intro h0
    have := hEig.qCoeff_one
    rw [h0, CuspForm.coe_zero, qCoeff_zero_fun] at this
    exact zero_ne_one this
  have hbound := CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen M 2 ε h hh0 hEig.2.2.2 hℓ' hℓ'M
    (ModularFormClass.qCoeff h ℓ') (fun n => hEig.hecke_of_not_dvd hℓ' hℓ'M n)
  rw [hqℓ, hc] at hbound
  have hnorm : ‖(ℓ' : ℂ) + 1‖ = (ℓ' : ℝ) + 1 := by
    rw [show (ℓ' : ℂ) + 1 = ((ℓ' + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring
  rw [hnorm, show (2 : ℤ) - 2 = 0 from by norm_num, zpow_zero, mul_one] at hbound
  exact lt_irrefl _ hbound

end Eigen
p2m_reactivate "P2MW.S_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL.RSplit"

end RSplit
p2m_reactivate "P2MW.S_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL.RSplit"

namespace RSplit

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∃ Q : Submodule ℂ (CohCarrier.H1 M H ℂ),
      IsCompl (ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) Q ∧
      Q ∈ Module.End.invtSubmodule (CohCarrier.heckeTL M H ℂ ℓ) := by
  classical

  obtain ⟨ℓ', hℓ'p, hℓ'gt, hℓ'1⟩ := Nat.exists_prime_gt_modEq_one M (NeZero.ne M)
  have hℓ'M : ¬ ℓ' ∣ M := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h) (not_le.mpr hℓ'gt)
  haveI : NeZero ℓ' := ⟨hℓ'p.ne_zero⟩
  set par := ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ with hpar
  set c : ℂ := (ℓ' : ℂ) + 1 with hc
  let E : Module.End ℂ (CohCarrier.H1 M H ℂ) := CohCarrier.heckeTL M H ℂ ℓ' - c • 1
  have hE : ∀ x, E x = CohCarrier.heckeTL M H ℂ ℓ' x - c • x := fun x => rfl

  have hEpar : ∀ x, E x ∈ par := by
    intro x
    have := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one M H ℂ x ℓ' hℓ'p hℓ'M hℓ'1
    rw [hE, CohCarrier.heckeTL_apply]
    have e1 : c • x = (ℓ' + 1) • x := by
      rw [hc, show ((ℓ' : ℂ) + 1) = ((ℓ' + 1 : ℕ) : ℂ) by push_cast; ring, Nat.cast_smul_eq_nsmul]
    rw [e1]
    exact this

  have hEinj : ∀ y ∈ par, E y = 0 → y = 0 := by
    intro y hy hEy
    rw [hE, sub_eq_zero] at hEy
    exact eq_zero_of_mem_par_of_heckeTL_eq M H hℓ'p hℓ'M y hy hEy

  let Q : Submodule ℂ (CohCarrier.H1 M H ℂ) := LinearMap.ker E
  refine ⟨Q, ?_, ?_⟩
  ·
    let Ep : ↥par →ₗ[ℂ] ↥par := E.restrict (p := par) (q := par) (fun y _ => hEpar y)
    have hEp_inj : Function.Injective Ep := by
      intro y z h
      apply Subtype.ext
      have : E (y - z : CohCarrier.H1 M H ℂ) = 0 := by
        have := congrArg Subtype.val h
        simp only [Ep, LinearMap.restrict_apply] at this
        rw [map_sub, this, sub_self]
      have := hEinj _ (par.sub_mem y.2 z.2) this
      exact sub_eq_zero.mp this
    have hEp_surj : Function.Surjective Ep := LinearMap.surjective_of_injective hEp_inj
    refine IsCompl.of_eq ?_ ?_
    · rw [Submodule.eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      exact hEinj x hx1 hx2
    · rw [Submodule.eq_top_iff']
      intro x
      obtain ⟨y, hy⟩ := hEp_surj ⟨E x, hEpar x⟩
      have hy' : E (y : CohCarrier.H1 M H ℂ) = E x := by
        have := congrArg Subtype.val hy
        simpa [Ep, LinearMap.restrict_apply] using this
      have hx : x = (y : CohCarrier.H1 M H ℂ) + (x - y) := by abel
      rw [hx]
      refine Submodule.add_mem_sup y.2 ?_
      show E (x - y) = 0
      rw [map_sub, hy', sub_self]
  ·
    intro x hx
    show E (CohCarrier.heckeTL M H ℂ ℓ x) = 0
    have hx' : E x = 0 := hx
    rw [hE, heckeTL_comm M H hℓ'p hℓ x, ← LinearMap.map_smul, ← map_sub, ← hE, hx', map_zero]

end RSplit
p2m_reactivate "P2MW.S_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL.RSplit"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∃ Q : Submodule ℂ (CohCarrier.H1 M H ℂ),
      IsCompl (ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) Q ∧
      Q ∈ Module.End.invtSubmodule (CohCarrier.heckeTL M H ℂ ℓ) :=
  RSplit.main M H hℓ hℓM

end S_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL
end P2MW
export P2MW.S_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL (solution)
