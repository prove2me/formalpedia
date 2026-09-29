-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c22caa99-cbce-525c-9ca3-1faecab1069f

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul
import Theorems.Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
import Theorems.Thm_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
import Theorems.Thm_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj
import Theorems.Thm_CuspForm_IsEigenformWith_fg_adjoin_qCoeff
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false
open scoped TensorProduct

namespace E2E
namespace C

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped MatrixGroups ModularForm ComplexConjugate

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QExp

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem cusp_periodic (F : CuspForm (Γ₁ℝ M) k) : Periodic (⇑F ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M)

theorem cusp_holo (F : CuspForm (Γ₁ℝ M) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd (F : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact CuspFormClass.zero_at_infty F |>.boundedAtFilter

theorem cusp_ext_of_qCoeff {F G : CuspForm (Γ₁ℝ M) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem analyticAt_cuspFunction (F : CuspForm (Γ₁ℝ M) k) : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)

theorem qCoeff_smul (c : ℂ) (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analyticAt_cuspFunction F) c, map_smul,
    smul_eq_mul]

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ M) k)) n = 0 := by
  rw [qCoeff, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

theorem exists_qCoeff_ne_zero {F : CuspForm (Γ₁ℝ M) k} (hF : F ≠ 0) : ∃ n : ℕ, qCoeff (⇑F) n ≠ 0 := by
  by_contra h
  push Not at h
  exact hF (cusp_ext_of_qCoeff fun n => by rw [h n, qCoeff_zero'])

end QExp

section Character

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem dirichlet_pow_totient (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    χ (ℓ : ZMod M) ^ Nat.totient M = 1 := by
  rw [← ZMod.coe_unitOfCoprime ℓ hℓ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
    Units.val_one, map_one]

theorem totient_ne_zero : Nat.totient M ≠ 0 := (Nat.totient_pos.2 (NeZero.pos M)).ne'

theorem dirichlet_ne_zero (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    χ (ℓ : ZMod M) ≠ 0 := fun h0 => by
  have h := dirichlet_pow_totient χ hℓ
  rw [h0, zero_pow totient_ne_zero] at h
  exact zero_ne_one h

theorem conj_dirichlet (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    conj (χ (ℓ : ZMod M)) = (χ (ℓ : ZMod M))⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (dirichlet_pow_totient χ hℓ)
    totient_ne_zero)).symm

omit [NeZero M] in
theorem inv_apply_dirichlet (χ : DirichletCharacter ℂ M) (ℓ : ℕ) :
    χ⁻¹ (ℓ : ZMod M) = (χ (ℓ : ZMod M))⁻¹ :=
  MulChar.inv_apply_eq_inv' χ _

end Character

section Main

p2m_open "CuspForm ModularForm.CuspForm"

variable {M : ℕ} [NeZero M]

omit [NeZero M] in

theorem qCoeff_relation {N : ℕ} (v : CuspForm (Gamma1 N) 2) (aT dD : ℕ → ℂ)
    (hT : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), CuspForm.heckeTLinOne 2 hp hpN v = aT p • v)
    (hD : ∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = dD d • v)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (n : ℕ) :
    qCoeff (⇑v) (p * n) + (p : ℂ) ^ ((2 : ℤ) - 1) * dD p * (if p ∣ n then qCoeff (⇑v) (n / p) else 0) =
      aT p * qCoeff (⇑v) n := by
  have h1 := congrArg (fun F : CuspForm (Gamma1 N) 2 => qCoeff (⇑F) n) (hT p hp hpN)
  rw [qCoeff_smul, CuspForm.qCoeff_heckeTLinOne 2 hp hpN v n,
    hD p ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN), qCoeff_smul] at h1
  rw [← h1]
  split_ifs <;> ring

private theorem _root_.E2E.C.ending
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (N : ℕ) [NeZero N] (hNM : N ∣ M) (S : Finset ℕ)
    (v : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hv0 : v ≠ 0)
    (aT : ℕ → ℂ) (dD : ℕ → ℂ)
    (hT : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), CuspForm.heckeTLinOne 2 hp hpN v = aT p • v)
    (hD : ∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = dD d • v)
    (hTval : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → aT ℓ = ModularFormClass.qCoeff g ℓ * (ε (ℓ : ZMod M))⁻¹)
    (hDval : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → dD ℓ = (ε (ℓ : ZMod M))⁻¹) :
    CuspForm.EigenpacketOccursAt 2 (fun n => ModularFormClass.qCoeff g n) (fun n => ε (n : ZMod M)) N := by
  classical

  obtain ⟨h, -, hq⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj N 2 v

  have hrel : ∀ (p : ℕ), p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      qCoeff (⇑h) (p * n) + (p : ℂ) ^ ((2 : ℤ) - 1) * conj (dD p) * (if p ∣ n then qCoeff (⇑h) (n / p) else 0) =
        conj (aT p) * qCoeff (⇑h) n := by
    intro p hp hpN n
    have hv := congrArg conj (qCoeff_relation v aT dD hT hD hp hpN n)
    rw [map_add, map_mul, map_mul, map_mul] at hv
    rw [hq (p * n), hq n]
    have hpow : conj ((p : ℂ) ^ ((2 : ℤ) - 1)) = (p : ℂ) ^ ((2 : ℤ) - 1) := by
      rw [map_zpow₀, Complex.conj_natCast]
    rw [hpow] at hv
    convert hv using 3
    split_ifs with hpn
    · rw [hq]
    · rw [map_zero]

  have hh0 : h ≠ 0 := by
    obtain ⟨n, hn⟩ := exists_qCoeff_ne_zero hv0
    intro h0
    apply hn
    have : qCoeff (⇑h) n = 0 := by rw [h0, qCoeff_zero']
    rw [hq n] at this
    simpa using congrArg conj this

  obtain ⟨ε'', hneb, hε''⟩ := CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen N 2 h hh0
    (fun p => (p : ℂ) ^ ((2 : ℤ) - 1) * conj (dD p))
    (fun p hp hpN => ⟨conj (aT p), hrel p hp hpN⟩)

  have hε''val : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ε'' (p : ZMod N) = conj (dD p) := by
    intro p hp hpN
    have hpp : ((p : ℂ) ^ ((2 : ℤ) - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    have := hε'' p hp hpN
    rw [mul_comm ((p : ℂ) ^ ((2 : ℤ) - 1))] at this
    exact mul_right_cancel₀ hpp this

  have hgE := hg.isEigenformWith
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 := hgE.qCoeff_one
    rw [h0, qCoeff_zero'] at h1
    exact zero_ne_one h1

  refine ⟨ε'', h, hh0, hneb, S ∪ M.primeFactors, ?_⟩
  intro p hp hpS
  rw [Finset.mem_union, not_or] at hpS
  have hpM : ¬ p ∣ M := fun hdvd => hpS.2 (Nat.mem_primeFactors.mpr ⟨hp, hdvd, NeZero.ne M⟩)
  have hpN : ¬ p ∣ N := fun hdvd => hpM (hdvd.trans hNM)
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM

  have hd : conj (dD p) = ε (p : ZMod M) := by
    rw [hDval p hp hpM hpS.1, map_inv₀, conj_dirichlet ε hcop, inv_inv]

  have ha : conj (aT p) = ModularFormClass.qCoeff g p := by
    have hc := CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M 2 ε g hg0 hgE.hasNebentypus p hp hpM
      (ModularFormClass.qCoeff g p) (fun n => hgE.hecke_of_not_dvd hp hpM n)
    rw [hTval p hp hpM hpS.1, map_mul, hc, map_inv₀, conj_dirichlet ε hcop, inv_inv,
      inv_apply_dirichlet, mul_comm ((ε (p : ZMod M))⁻¹), mul_assoc,
      inv_mul_cancel₀ (dirichlet_ne_zero ε hcop), mul_one]
  refine ⟨by rw [hε''val p hp hpN, hd], fun n => ?_⟩
  have := hrel p hp hpN n
  rw [ha, ← hε''val p hp hpN] at this
  rw [← this]
  ring

p2m_export "E2E.C" "ending"
end Main

end E2E.C

namespace E2E

private theorem _root_.E2E.ending
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (N : ℕ) [NeZero N] (hNM : N ∣ M) (S : Finset ℕ)
    (v : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hv0 : v ≠ 0)
    (aT : ℕ → ℂ) (dD : ℕ → ℂ)
    (hT : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), CuspForm.heckeTLinOne 2 hp hpN v = aT p • v)
    (hD : ∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = dD d • v)
    (hTval : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → aT ℓ = ModularFormClass.qCoeff g ℓ * (ε (ℓ : ZMod M))⁻¹)
    (hDval : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → dD ℓ = (ε (ℓ : ZMod M))⁻¹) :
    CuspForm.EigenpacketOccursAt 2 (fun n => ModularFormClass.qCoeff g n) (fun n => ε (n : ZMod M)) N :=
  E2E.C.ending hg N hNM S v hv0 aT dD hT hD hTval hDval

end E2E
p2m_export "" "E2E.ending"
noncomputable section

namespace E2E93

open Module Module.End Set

open Submodule in
theorem transfer_relation
    {P T E Ω F : Type} [Field F] [CharZero F]
    [AddCommGroup P] [AddCommGroup T] [AddCommGroup E] [Module F E]
    [AddCommGroup Ω] [Module F Ω]
    (α : P →+ T) (β : P →+ Ω) (hαβ : ∀ g, α g = 0 → β g = 0)
    (γ : T →+ E)
    (hγ : ∀ {ι : Type} (u : ι → T), LinearIndependent ℤ u → LinearIndependent F (fun i => γ (u i)))
    {κ : Type} [Fintype κ] (x : κ → P) (c : κ → F)
    (hf : ∑ k, c k • γ (α (x k)) = 0) :
    ∑ k, c k • β (x k) = 0 := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (fun k => α (x k))
  have hrel : ∀ k, ∃ r : ℤ, r ≠ 0 ∧ ∃ a : s → ℤ, ∑ j : s, a j • α (x j) = r • α (x k) := by
    intro k
    by_cases hk : k ∈ s
    · refine ⟨1, one_ne_zero, Pi.single ⟨k, hk⟩ 1, ?_⟩
      rw [one_smul, Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_smul]
    · obtain ⟨r, hr, hmem⟩ := hmax k hk
      rw [Set.image_eq_range] at hmem
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
      exact ⟨r, hr, a, ha⟩
  choose r hr a ha using hrel
  have hli : LinearIndependent F (fun j : s => γ (α (x j))) := hγ _ hs
  have hr' : ∀ k, (r k : F) ≠ 0 := fun k => Int.cast_ne_zero.2 (hr k)
  have hvan : ∀ k, α (∑ j : s, a k j • x j - r k • x k) = 0 := fun k => by
    rw [map_sub, map_sum, map_zsmul]
    simp_rw [map_zsmul]
    rw [ha, sub_self]
  have hγrel : ∀ k, γ (α (x k)) = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • γ (α (x j)) := fun k => by
    rw [eq_inv_smul_iff₀ (hr' k), Int.cast_smul_eq_zsmul, ← map_zsmul, ← ha k, map_sum]
    simp_rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hβrel : ∀ k, β (x k) = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • β (x j) := fun k => by
    have h := hαβ _ (hvan k)
    rw [map_sub, sub_eq_zero, map_sum, map_zsmul] at h
    rw [eq_inv_smul_iff₀ (hr' k), Int.cast_smul_eq_zsmul, ← h]
    simp_rw [map_zsmul, Int.cast_smul_eq_zsmul]
  set d : s → F := fun j => ∑ k, c k * ((r k : F)⁻¹ * (a k j : F)) with hd
  have key : ∀ {X : Type} [AddCommGroup X] [Module F X] (φ : κ → X) (ψ : s → X),
      (∀ k, φ k = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • ψ j) →
        ∑ k, c k • φ k = ∑ j, d j • ψ j := by
    intro X _ _ φ ψ h
    calc ∑ k, c k • φ k = ∑ k, ∑ j, (c k * ((r k : F)⁻¹ * (a k j : F))) • ψ j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [h k, Finset.smul_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul, smul_smul, mul_assoc]
      _ = ∑ j, ∑ k, (c k * ((r k : F)⁻¹ * (a k j : F))) • ψ j := Finset.sum_comm
      _ = ∑ j, d j • ψ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hd, Finset.sum_smul]
  have hd0 : ∀ j, d j = 0 := by
    have h0 : ∑ j, d j • γ (α (x j)) = 0 := by
      rw [← key (fun k => γ (α (x k))) (fun j => γ (α (x j))) hγrel]
      exact hf
    exact Fintype.linearIndependent_iff.1 hli d h0
  rw [key (fun k => β (x k)) (fun j => β (x j)) hβrel]
  simp [hd0]

theorem algHom_eq_sum_coeff_smul {I F C : Type*} [Field F] [Ring C] [Algebra F C]
    (e : MvPolynomial I F →ₐ[F] C) (f : MvPolynomial I F) :
    e f = ∑ m ∈ f.support,
      MvPolynomial.coeff m f • e (MvPolynomial.map (Int.castRingHom F) (MvPolynomial.monomial m 1)) := by
  conv_lhs => rw [f.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, map_one, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul,
    mul_one]

section Rational

variable {ι : Type} {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem exists_ratRetraction : ∃ π : ℂ →ₗ[ℚ] ℚ, ∀ q : ℚ, π (algebraMap ℚ ℂ q) = q := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ ℂ).injective)
  exact ⟨g, fun q => by simpa using LinearMap.congr_fun hg q⟩

def RatOp (bs : Basis (Fin n) ℂ V) (T : Module.End ℂ V) : Prop :=
  ∀ j k : Fin n, bs.repr (T (bs j)) k ∈ Set.range (algebraMap ℚ ℂ)

theorem repr_apply_eq_sum (bs : Basis (Fin n) ℂ V)
    (T : Module.End ℂ V) (v : V) (k : Fin n) :
    bs.repr (T v) k = ∑ j, bs.repr v j * bs.repr (T (bs j)) k := by
  have h : T v = ∑ j, bs.repr v j • T (bs j) := by
    conv_lhs => rw [← bs.sum_repr v]
    rw [map_sum]
    simp_rw [map_smul]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  simp_rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem ratOp_one (bs : Basis (Fin n) ℂ V) : RatOp bs 1 := by
  intro j k
  refine ⟨if j = k then 1 else 0, ?_⟩
  rw [Module.End.one_apply, bs.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem ratOp_intCast (bs : Basis (Fin n) ℂ V) (a : ℤ) : RatOp bs (a : Module.End ℂ V) := by
  intro j k
  obtain ⟨q, hq⟩ := ratOp_one bs j k
  refine ⟨a * q, ?_⟩
  rw [Module.End.intCast_apply, ← Module.End.one_apply (R := ℂ) (bs j), map_zsmul, Finsupp.smul_apply,
    ← hq, zsmul_eq_mul, map_mul, map_intCast]

theorem RatOp.add {bs : Basis (Fin n) ℂ V} {T T' : Module.End ℂ V} (h : RatOp bs T) (h' : RatOp bs T') :
    RatOp bs (T + T') := by
  intro j k
  obtain ⟨q, hq⟩ := h j k
  obtain ⟨q', hq'⟩ := h' j k
  refine ⟨q + q', ?_⟩
  simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, ← hq, ← hq']

theorem RatOp.mul {bs : Basis (Fin n) ℂ V} {T T' : Module.End ℂ V} (h : RatOp bs T) (h' : RatOp bs T') :
    RatOp bs (T * T') := by
  intro j k
  choose q hq using h
  choose q' hq' using h'
  refine ⟨∑ l, q' j l * q l k, ?_⟩
  rw [Module.End.mul_apply, repr_apply_eq_sum bs T (T' (bs j)) k, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, hq, hq']

theorem ratOp_of_poly (bs : Basis (Fin n) ℂ V) (Φz : MvPolynomial ι ℤ →+* Module.End ℂ V)
    (hrat : ∀ i, RatOp bs (Φz (MvPolynomial.X i))) (P : MvPolynomial ι ℤ) : RatOp bs (Φz P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [eq_intCast MvPolynomial.C, map_intCast]; exact ratOp_intCast bs a
  | add f g hf hg => rw [map_add]; exact hf.add hg
  | mul_X f i hf => rw [map_mul]; exact hf.mul (hrat i)

def ratMatrix (bs : Basis (Fin n) ℂ V) (π : ℂ →ₗ[ℚ] ℚ) (T : Module.End ℂ V) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun k j => π (bs.repr (T (bs j)) k)

def ratMatrixHom (bs : Basis (Fin n) ℂ V) (π : ℂ →ₗ[ℚ] ℚ) :
    Module.End ℂ V →+ Matrix (Fin n) (Fin n) ℚ where
  toFun := ratMatrix bs π
  map_zero' := by ext k j; simp [ratMatrix]
  map_add' T T' := by ext k j; simp [ratMatrix, map_add]

def realise (bs : Basis (Fin n) ℂ V) : Matrix (Fin n) (Fin n) ℚ →+ Module.End ℂ V :=
  (Matrix.toLin bs bs).toLinearMap.toAddMonoidHom.comp
    ((algebraMap ℚ ℂ).mapMatrix : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) ℂ).toAddMonoidHom

theorem realise_apply (bs : Basis (Fin n) ℂ V) (A : Matrix (Fin n) (Fin n) ℚ) :
    realise bs A = Matrix.toLin bs bs (A.map (algebraMap ℚ ℂ)) := rfl

theorem realise_ratMatrix (bs : Basis (Fin n) ℂ V) {π : ℂ →ₗ[ℚ] ℚ}
    (hπ : ∀ q : ℚ, π (algebraMap ℚ ℂ q) = q) {T : Module.End ℂ V} (hT : RatOp bs T) :
    realise bs (ratMatrix bs π T) = T := by
  have hentry : ∀ k j, algebraMap ℚ ℂ (π (bs.repr (T (bs j)) k)) = bs.repr (T (bs j)) k := by
    intro k j
    obtain ⟨q, hq⟩ := hT j k
    rw [← hq, hπ]
  refine bs.ext fun j => ?_
  rw [realise_apply, Matrix.toLin_self]
  conv_rhs => rw [← bs.sum_repr (T (bs j))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, ratMatrix, Matrix.of_apply, hentry]

theorem linearIndependent_map_matrix {κ : Type} (u : κ → Matrix (Fin n) (Fin n) ℚ)
    (hu : LinearIndependent ℚ u) :
    LinearIndependent ℂ (fun t => (u t).map (algebraMap ℚ ℂ)) := by
  classical
  rw [linearIndependent_iff'] at hu ⊢
  intro s c hc t ht

  refine (Module.forall_dual_apply_eq_zero_iff ℚ (c t)).1 fun φ => ?_
  have hφ : ∑ t ∈ s, φ (c t) • u t = 0 := by
    ext k j
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => φ (A k j)) hc
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, map_zero,
      smul_eq_mul] at h
    rw [Matrix.sum_apply, Matrix.zero_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← h, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul, smul_eq_mul, mul_comm]
  exact hu s (fun t => φ (c t)) hφ t ht

theorem realise_linearIndependent (bs : Basis (Fin n) ℂ V) {κ : Type} (u : κ → Matrix (Fin n) (Fin n) ℚ)
    (hu : LinearIndependent ℤ u) : LinearIndependent ℂ (fun t => realise bs (u t)) := by
  have hu' : LinearIndependent ℚ u := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hu
  have h1 := linearIndependent_map_matrix u hu'
  have h2 := h1.map' (Matrix.toLin bs bs).toLinearMap (LinearEquiv.ker _)
  exact h2

theorem complexRelations (bs : Basis (Fin n) ℂ V) (Φz : MvPolynomial ι ℤ →+* Module.End ℂ V)
    (hrat : ∀ i, RatOp bs (Φz (MvPolynomial.X i)))
    (ΦC : MvPolynomial ι ℂ →ₐ[ℂ] Module.End ℂ V) (hΦC : ∀ i, ΦC (MvPolynomial.X i) = Φz (MvPolynomial.X i))
    (μc : MvPolynomial ι ℤ →+* ℂ) (hK0 : ∀ P : MvPolynomial ι ℤ, Φz P = 0 → μc P = 0)
    (P : MvPolynomial ι ℂ) (hP : ΦC P = 0) :
    MvPolynomial.aeval (fun i => μc (MvPolynomial.X i)) P = 0 := by
  classical
  obtain ⟨π, hπ⟩ := exists_ratRetraction

  have hcompat : ∀ Q : MvPolynomial ι ℤ, ΦC (MvPolynomial.map (Int.castRingHom ℂ) Q) = Φz Q := by
    intro Q
    have key : ΦC.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℂ)) = Φz :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by
        show ΦC (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.X i)) = Φz (MvPolynomial.X i)
        rw [MvPolynomial.map_X, hΦC])
    exact RingHom.congr_fun key Q
  let eχ : MvPolynomial ι ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun i => μc (MvPolynomial.X i))
  have hcompat' : ∀ Q : MvPolynomial ι ℤ, eχ (MvPolynomial.map (Int.castRingHom ℂ) Q) = μc Q := by
    intro Q
    have key : eχ.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℂ)) = μc :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by
        show eχ (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.X i)) = μc (MvPolynomial.X i)
        rw [MvPolynomial.map_X]
        exact MvPolynomial.aeval_X _ i)
    exact RingHom.congr_fun key Q

  have hT := transfer_relation (F := ℂ) ((ratMatrixHom bs π).comp Φz.toAddMonoidHom) μc.toAddMonoidHom
    (fun Q hQ => by
      have hreal := realise_ratMatrix bs hπ (ratOp_of_poly bs Φz hrat Q)
      have hQ' : ratMatrix bs π (Φz Q) = 0 := hQ
      rw [hQ', map_zero] at hreal
      show μc Q = 0
      exact hK0 Q hreal.symm)
    (realise bs) (fun u hu => realise_linearIndependent bs u hu)
    (fun m : ↥P.support => (MvPolynomial.monomial (m : ι →₀ ℕ) (1 : ℤ) : MvPolynomial ι ℤ))
    (fun m => MvPolynomial.coeff (m : ι →₀ ℕ) P)
    (by
      have h1 : ∀ m : ↥P.support,
          realise bs (((ratMatrixHom bs π).comp Φz.toAddMonoidHom)
            (MvPolynomial.monomial (m : ι →₀ ℕ) (1 : ℤ)))
            = ΦC (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.monomial (m : ι →₀ ℕ) 1)) := by
        intro m
        rw [hcompat]
        exact realise_ratMatrix bs hπ (ratOp_of_poly bs Φz hrat _)
      simp_rw [h1]
      rw [Finset.sum_coe_sort P.support (fun m => MvPolynomial.coeff m P •
        ΦC (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.monomial m 1)))]
      rw [← algHom_eq_sum_coeff_smul ΦC P]
      exact hP)
  show eχ P = 0
  rw [algHom_eq_sum_coeff_smul eχ P, ← Finset.sum_coe_sort]
  refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hT
  rw [hcompat']
  rfl

theorem isAlgebraic_of_relations (bs : Basis (Fin n) ℂ V) (Φz : MvPolynomial ι ℤ →+* Module.End ℂ V)
    (hrat : ∀ i, RatOp bs (Φz (MvPolynomial.X i)))
    {Ω : Type} [Field Ω] [CharZero Ω]
    (μ : MvPolynomial ι ℤ →+* Ω) (hK0 : ∀ P : MvPolynomial ι ℤ, Φz P = 0 → μ P = 0) (i : ι) :
    IsAlgebraic ℚ (μ (MvPolynomial.X i)) := by
  classical
  obtain ⟨π, hπ⟩ := exists_ratRetraction
  set A : Matrix (Fin n) (Fin n) ℚ := ratMatrix bs π (Φz (MvPolynomial.X i)) with hA
  have hreal : Matrix.toLin bs bs (A.map (algebraMap ℚ ℂ)) = Φz (MvPolynomial.X i) :=
    realise_ratMatrix bs hπ (hrat i)
  set q : Polynomial ℚ := A.charpoly with hq

  have hCH : Polynomial.aeval (Φz (MvPolynomial.X i)) (q.map (algebraMap ℚ ℂ)) = 0 := by
    have h1 : Polynomial.aeval (A.map (algebraMap ℚ ℂ)) (q.map (algebraMap ℚ ℂ)) = 0 := by
      rw [hq, ← Matrix.charpoly_map]; exact Matrix.aeval_self_charpoly _
    have h2 := congrArg (Matrix.toLinAlgEquiv bs).toAlgHom h1
    rw [← Polynomial.aeval_algHom_apply, map_zero] at h2
    rw [← hreal]
    exact h2

  set Q : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q with hQ
  obtain ⟨b, hb, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := (IsLocalization.integerNormalization_eq_zero_iff (M := nonZeroDivisors ℤ) le_rfl q).1 h0
    exact (Matrix.charpoly_monic A).ne_zero this

  have hΦQ : Φz (Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι ℤ) Q) = 0 := by
    have e1 : Φz (Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι ℤ) Q)
        = Polynomial.aeval (Φz (MvPolynomial.X i)) Q :=
      (Polynomial.aeval_algHom_apply Φz.toIntAlgHom (MvPolynomial.X i) Q).symm
    have e2 : Q.map (algebraMap ℤ ℂ) = b • q.map (algebraMap ℚ ℂ) := by
      rw [← RingHom.ext_int ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)) (algebraMap ℤ ℂ),
        ← Polynomial.map_map, hbQ]
      exact map_zsmul (Polynomial.mapRingHom (algebraMap ℚ ℂ)) b q
    rw [e1, ← Polynomial.aeval_map_algebraMap ℂ (Φz (MvPolynomial.X i)) Q, e2, map_zsmul, hCH,
      smul_zero]
  have hμQ : Polynomial.aeval (μ (MvPolynomial.X i)) Q = 0 := by
    have e1 : μ (Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι ℤ) Q)
        = Polynomial.aeval (μ (MvPolynomial.X i)) Q :=
      (Polynomial.aeval_algHom_apply μ.toIntAlgHom (MvPolynomial.X i) Q).symm
    rw [← e1]
    exact hK0 _ hΦQ
  have halg : IsAlgebraic ℤ (μ (MvPolynomial.X i)) := ⟨Q, hQ0, hμQ⟩
  exact halg.extendScalars (R := ℤ) (S := ℚ) (algebraMap ℤ ℚ).injective_int

end Rational

section CommonKer

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_apply_mem {t : Module.End K V} {W : Submodule K V} (ht : ∀ w ∈ W, t w ∈ W)
    (k : ℕ) {w : V} (hw : w ∈ W) : (t ^ k) w ∈ W := by
  induction k with
  | zero => simpa using hw
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact ht _ ih

theorem exists_common_ker_finset [DecidableEq (Module.End K V)] (s : Finset (Module.End K V)) :
    ∀ W : Submodule K V, W ≠ ⊥ →
      (∀ t ∈ s, ∀ w ∈ W, t w ∈ W) →
      (∀ t ∈ s, ∃ k : ℕ, ∀ w ∈ W, (t ^ k) w = 0) →
      (∀ t ∈ s, ∀ t' ∈ s, Commute t t') →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ t ∈ s, t v = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro W hW _ _ _
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨v, hv, hv0, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  | insert a s ha ih =>
    intro W hW hstab hnil hcomm

    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨k, hk⟩ := hnil a (Finset.mem_insert_self a s)
    have hex : ∃ j : ℕ, (a ^ j) w = 0 := ⟨k, hk w hw⟩
    let j := Nat.find hex
    have hj : (a ^ j) w = 0 := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Module.End.one_apply] at hj
      exact hw0 hj
    obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    set u := (a ^ j') w with hu
    have hu0 : u ≠ 0 := by
      have hlt : j' < j := by rw [hj']; exact Nat.lt_succ_self j'
      exact Nat.find_min hex hlt
    have hau : a u = 0 := by
      have e : j' + 1 = j := by rw [hj']
      rw [hu, ← Module.End.mul_apply, ← pow_succ', e, hj]
    have huW : u ∈ W := pow_apply_mem (hstab a (Finset.mem_insert_self a s)) j' hw

    let W' : Submodule K V := W ⊓ LinearMap.ker a
    have hW' : W' ≠ ⊥ := by
      intro h
      have : u ∈ W' := ⟨huW, LinearMap.mem_ker.2 hau⟩
      rw [h] at this
      exact hu0 ((Submodule.mem_bot K).1 this)
    have hstab' : ∀ t ∈ s, ∀ w ∈ W', t w ∈ W' := by
      intro t ht w hw'
      refine ⟨hstab t (Finset.mem_insert_of_mem ht) w hw'.1, LinearMap.mem_ker.2 ?_⟩
      have hc := hcomm a (Finset.mem_insert_self a s) t (Finset.mem_insert_of_mem ht)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, LinearMap.mem_ker.1 hw'.2, map_zero]
    have hnil' : ∀ t ∈ s, ∃ k : ℕ, ∀ w ∈ W', (t ^ k) w = 0 := fun t ht => by
      obtain ⟨k, hk⟩ := hnil t (Finset.mem_insert_of_mem ht)
      exact ⟨k, fun w hw' => hk w hw'.1⟩
    have hcomm' : ∀ t ∈ s, ∀ t' ∈ s, Commute t t' := fun t ht t' ht' =>
      hcomm t (Finset.mem_insert_of_mem ht) t' (Finset.mem_insert_of_mem ht')
    obtain ⟨v, hv, hv0, hvs⟩ := ih W' hW' hstab' hnil' hcomm'
    refine ⟨v, hv.1, hv0, ?_⟩
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact LinearMap.mem_ker.1 hv.2
    · exact hvs t ht

theorem exists_common_ker [FiniteDimensional K V] {ι : Type*} (N : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (N i) (N j)) (W : Submodule K V) (hW : W ≠ ⊥)
    (hstab : ∀ i, ∀ w ∈ W, N i w ∈ W) (hnil : ∀ i, ∃ k : ℕ, ∀ w ∈ W, (N i ^ k) w = 0) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, N i v = 0 := by
  classical
  obtain ⟨B, hBT, hspan, hli⟩ := exists_linearIndependent K (Set.range N)
  have hfin : B.Finite := hli.setFinite
  let s : Finset (Module.End K V) := hfin.toFinset
  have hsB : ∀ t, t ∈ s ↔ t ∈ B := fun t => Set.Finite.mem_toFinset hfin
  have hmemN : ∀ t ∈ s, ∃ i, N i = t := fun t ht => hBT ((hsB t).1 ht)
  obtain ⟨v, hv, hv0, hvs⟩ := exists_common_ker_finset s W hW
    (fun t ht w hw => by obtain ⟨i, rfl⟩ := hmemN t ht; exact hstab i w hw)
    (fun t ht => by obtain ⟨i, rfl⟩ := hmemN t ht; exact hnil i)
    (fun t ht t' ht' => by
      obtain ⟨i, rfl⟩ := hmemN t ht; obtain ⟨j, rfl⟩ := hmemN t' ht'; exact hcomm i j)
  refine ⟨v, hv, hv0, fun i => ?_⟩
  have hi : N i ∈ Submodule.span K B := by
    rw [hspan]; exact Submodule.subset_span (Set.mem_range_self i)
  refine Submodule.span_induction (p := fun t _ => t v = 0) (fun t ht => hvs t ((hsB t).2 ht))
    (LinearMap.zero_apply v)
    (fun x y _ _ hx hy => show (x + y) v = 0 by rw [LinearMap.add_apply, hx, hy, add_zero])
    (fun c x _ hx => show (c • x) v = 0 by rw [LinearMap.smul_apply, hx, smul_zero]) hi

end CommonKer

section Character

variable {ι K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [IsAlgClosed K] [FiniteDimensional K V] in

theorem algHom_C (Φ : MvPolynomial ι K →ₐ[K] Module.End K V) (c : K) :
    Φ (MvPolynomial.C c) = c • (1 : Module.End K V) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_eq_smul_id]
  rfl

theorem exists_common_eigenvector (Φ : MvPolynomial ι K →ₐ[K] Module.End K V) (ν : ι → K)
    (hK : ∀ P : MvPolynomial ι K, Φ P = 0 → MvPolynomial.aeval ν P = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, Φ (MvPolynomial.X i) v = ν i • v := by
  classical
  set O : ι → Module.End K V := fun i => Φ (MvPolynomial.X i) with hOdef
  have hO : ∀ i j, Commute (O i) (O j) := fun i j => by
    show Φ (MvPolynomial.X i) * Φ (MvPolynomial.X j) = Φ (MvPolynomial.X j) * Φ (MvPolynomial.X i)
    rw [← map_mul, ← map_mul, mul_comm]

  let E : (ι → K) → Submodule K V := fun χ => ⨅ i, (O i).maxGenEigenspace (χ i)
  have hmaps : ∀ i j φ, MapsTo (O i) ((O j).maxGenEigenspace φ) ((O j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hO j i) φ
  have htop : ⨆ χ : ι → K, E χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo O hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (O i))
  have hind : iSupIndep E := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo O hmaps
  haveI : Fintype {χ // E χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  set n := Module.finrank K V with hn

  have hkill : ∀ (χ : ι → K) (i : ι) (x : V), x ∈ E χ →
      Φ ((MvPolynomial.X i - MvPolynomial.C (χ i)) ^ n) x = 0 := by
    intro χ i x hx
    have hxi : x ∈ (O i).maxGenEigenspace (χ i) := (Submodule.mem_iInf _).1 hx i
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat,
      LinearMap.mem_ker] at hxi
    rw [map_pow, map_sub, algHom_C]
    exact hxi

  have hEν : E ν ≠ ⊥ := by
    intro hbot
    have hsep : ∀ χ : {χ // E χ ≠ ⊥}, ∃ i, ν i ≠ χ.1 i := by
      intro χ
      by_contra h
      push Not at h
      have hχν : χ.1 = ν := (funext h).symm
      exact χ.2 (hχν ▸ hbot)
    choose iχ hiχ using hsep
    let P : MvPolynomial ι K :=
      ∏ χ : {χ // E χ ≠ ⊥}, (MvPolynomial.X (iχ χ) - MvPolynomial.C (χ.1 (iχ χ))) ^ n
    have hPO : Φ P = 0 := by
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ ⨆ χ, E χ := by rw [htop]; exact Submodule.mem_top
      rw [LinearMap.zero_apply]
      refine Submodule.iSup_induction E (motive := fun x => Φ P x = 0) hv
        (fun χ x hx => ?_) (map_zero _)
        (fun x y hx hy => show Φ P (x + y) = 0 by rw [map_add, hx, hy, add_zero])
      by_cases hχ : E χ = ⊥
      · rw [hχ] at hx
        rw [(Submodule.mem_bot K).1 hx, map_zero]
      · have hmem : (⟨χ, hχ⟩ : {χ // E χ ≠ ⊥}) ∈ (Finset.univ : Finset {χ // E χ ≠ ⊥}) :=
          Finset.mem_univ _
        show Φ (∏ χ' : {χ // E χ ≠ ⊥},
          (MvPolynomial.X (iχ χ') - MvPolynomial.C (χ'.1 (iχ χ'))) ^ n) x = 0
        rw [← Finset.prod_erase_mul _ _ hmem, map_mul, Module.End.mul_apply, hkill χ (iχ ⟨χ, hχ⟩) x hx,
          map_zero]
    have hPν : MvPolynomial.aeval ν P ≠ 0 := by
      rw [map_prod]
      refine Finset.prod_ne_zero_iff.2 fun χ _ => ?_
      rw [map_pow]
      refine pow_ne_zero _ ?_
      rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
      exact sub_ne_zero.2 (hiχ χ)
    exact hPν (hK P hPO)

  have hstab : ∀ i, ∀ w ∈ E ν, (O i - ν i • 1) w ∈ E ν := by
    intro i w hw
    refine (Submodule.mem_iInf _).2 fun j => ?_
    have hwj : w ∈ (O j).maxGenEigenspace (ν j) := (Submodule.mem_iInf _).1 hw j
    have h1 : O i w ∈ (O j).maxGenEigenspace (ν j) := hmaps i j (ν j) hwj
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ hwj)
  have hnil : ∀ i, ∃ k : ℕ, ∀ w ∈ E ν, ((O i - ν i • 1) ^ k) w = 0 := by
    intro i
    refine ⟨n, fun w hw => ?_⟩
    have hwi : w ∈ (O i).maxGenEigenspace (ν i) := (Submodule.mem_iInf _).1 hw i
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat,
      LinearMap.mem_ker] at hwi
    exact hwi
  have hcommN : ∀ i j, Commute (O i - ν i • 1) (O j - ν j • 1) := by
    intro i j
    have e : ∀ i, O i - ν i • (1 : Module.End K V) = Φ (MvPolynomial.X i - MvPolynomial.C (ν i)) :=
      fun i => by rw [map_sub, algHom_C]
    rw [e, e]
    show Φ _ * Φ _ = Φ _ * Φ _
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨v, -, hv0, hv⟩ := exists_common_ker (fun i => O i - ν i • 1) hcommN (E ν) hEν hstab hnil
  refine ⟨v, hv0, fun i => ?_⟩
  have h := hv i
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

end Character

section QExp

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem cusp_periodic (F : CuspForm (Γ₁ℝ M) k) : Periodic (⇑F ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M)

theorem cusp_holo (F : CuspForm (Γ₁ℝ M) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd (F : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty F

theorem cusp_ext_of_qCoeff {F G : CuspForm (Γ₁ℝ M) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem analyticAt_cuspFunction (F : CuspForm (Γ₁ℝ M) k) : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)

theorem qCoeff_smul (c : ℂ) (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analyticAt_cuspFunction F) c, map_smul,
    smul_eq_mul]

theorem qCoeff_add (F G : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(F + G)) n = qCoeff (⇑F) n + qCoeff (⇑G) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_add,
    qExpansion_add (analyticAt_cuspFunction F) (analyticAt_cuspFunction G), map_add]

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ M) k)) n = 0 := by
  rw [qCoeff, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_sum {ι : Type} (s : Finset ι) (F : ι → CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, F i)) n = ∑ i ∈ s, qCoeff (⇑(F i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qCoeff_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qCoeff_add, ih]

theorem ne_zero_of_qCoeff_one (F : CuspForm (Γ₁ℝ M) k) (h1 : qCoeff (⇑F) 1 = 1) : F ≠ 0 := by
  rintro rfl
  rw [qCoeff_zero'] at h1
  exact zero_ne_one h1

theorem repr_rational_of_qCoeff_rational {n : ℕ} (bs : Basis (Fin n) ℂ (CuspForm (Γ₁ℝ M) k))
    (hbs : ∀ (i : Fin n) (m : ℕ), qCoeff (⇑(bs i)) m ∈ Set.range (algebraMap ℚ ℂ))
    (F : CuspForm (Γ₁ℝ M) k) (hF : ∀ m : ℕ, qCoeff (⇑F) m ∈ Set.range (algebraMap ℚ ℂ)) (i : Fin n) :
    bs.repr F i ∈ Set.range (algebraMap ℚ ℂ) := by
  classical
  obtain ⟨π, hπ⟩ := exists_ratRetraction
  choose rb hrb using hbs
  choose rF hrF using hF

  let F' : CuspForm (Γ₁ℝ M) k := ∑ j, algebraMap ℚ ℂ (π (bs.repr F j)) • bs j
  have hF' : ∀ m, qCoeff (⇑F') m = qCoeff (⇑F) m := by
    intro m
    have hFsum : F = ∑ j, bs.repr F j • bs j := (bs.sum_repr F).symm
    have h1 : qCoeff (⇑F) m = ∑ j, bs.repr F j * qCoeff (⇑(bs j)) m := by
      conv_lhs => rw [hFsum]
      rw [qCoeff_sum]
      simp_rw [qCoeff_smul]
    have h2 : qCoeff (⇑F') m = ∑ j, algebraMap ℚ ℂ (π (bs.repr F j)) * qCoeff (⇑(bs j)) m := by
      show qCoeff (⇑(∑ j, algebraMap ℚ ℂ (π (bs.repr F j)) • bs j)) m = _
      rw [qCoeff_sum]
      simp_rw [qCoeff_smul]

    have h3 : rF m = ∑ j, rb j m * π (bs.repr F j) := by
      have e : rF m = π (qCoeff (⇑F) m) := by rw [← hrF m, hπ]
      rw [e, h1, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hrb j m, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
    rw [h2, ← hrF m, h3, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hrb, mul_comm]
  have hFF' : F' = F := cusp_ext_of_qCoeff hF'
  refine ⟨π (bs.repr F i), ?_⟩
  have h := congrArg (fun G => bs.repr G i) hFF'
  simp only [F', map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, bs.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  exact h

end QExp

section Cusp

open CongruenceSubgroup ModularForm ModularFormClass
open scoped MatrixGroups ModularForm ComplexConjugate

variable {M : ℕ} [NeZero M]

omit [NeZero M] in

theorem diamond_eigen {χ : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith χ h) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.diamondLinOne M 2 ℓ h = χ (ℓ : ZMod M) • h :=
  hh.hasNebentypus.diamondLinOne_apply_eq_smul ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)

omit [NeZero M] in

theorem hecke_eigen {χ : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith χ h) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.heckeTLinOne 2 hℓ hℓM h = qCoeff (⇑h) ℓ • h := by
  refine cusp_ext_of_qCoeff fun n => ?_
  rw [CuspForm.qCoeff_heckeTLinOne 2 hℓ hℓM h n, diamond_eigen hh hℓ hℓM, qCoeff_smul, qCoeff_smul,
    ← hh.hecke_of_not_dvd hℓ hℓM n]
  split_ifs <;> ring

omit [NeZero M] in

theorem heckeU_eigen {χ : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith χ h) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M)
    (U : Module.End ℂ (CuspForm (Gamma1 M) 2)) (hU : ∀ f n, qCoeff (⇑(U f)) n = qCoeff (⇑f) (ℓ * n)) :
    U h = qCoeff (⇑h) ℓ • h := by
  refine cusp_ext_of_qCoeff fun n => ?_
  rw [hU, qCoeff_smul, hh.hecke_of_dvd hℓ hℓM n]

omit [NeZero M] in

theorem dirichlet_pow_totient (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    χ (ℓ : ZMod M) ^ Nat.totient M = 1 := by
  rw [← ZMod.coe_unitOfCoprime ℓ hℓ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
    Units.val_one, map_one]

theorem totient_ne_zero : Nat.totient M ≠ 0 := (Nat.totient_pos.2 (NeZero.pos M)).ne'

theorem dirichlet_ne_zero (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    χ (ℓ : ZMod M) ≠ 0 := fun h0 => by
  have h := dirichlet_pow_totient χ hℓ
  rw [h0, zero_pow totient_ne_zero] at h
  exact zero_ne_one h

theorem conj_dirichlet (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    conj (χ (ℓ : ZMod M)) = (χ (ℓ : ZMod M))⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (dirichlet_pow_totient χ hℓ)
    totient_ne_zero)).symm

omit [NeZero M] in
theorem inv_apply_dirichlet (χ : DirichletCharacter ℂ M) (ℓ : ℕ) :
    χ⁻¹ (ℓ : ZMod M) = (χ (ℓ : ZMod M))⁻¹ :=
  MulChar.inv_apply_eq_inv' χ _

theorem dirichlet_ext {χ₁ χ₂ : DirichletCharacter ℂ M} (S : Finset ℕ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → χ₁ (ℓ : ZMod M) = χ₂ (ℓ : ZMod M)) : χ₁ = χ₂ := by
  refine MulChar.ext fun u => ?_
  obtain ⟨ℓ, hℓgt, hℓp, hℓu⟩ := Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit u) (S.sup id)
  have hℓS : ℓ ∉ S := fun hmem => by
    have : ℓ ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  have hcop : Nat.Coprime ℓ M := by
    have hu : IsUnit ((ℓ : ℕ) : ZMod M) := by rw [hℓu]; exact Units.isUnit u
    exact (ZMod.isUnit_iff_coprime ℓ M).1 hu
  have hℓM : ¬ ℓ ∣ M := fun hdvd => by
    have := Nat.Coprime.eq_one_of_dvd hcop hdvd
    exact hℓp.one_lt.ne' this
  rw [← hℓu]
  exact h ℓ hℓp hℓM hℓS

theorem eigenvalue_eq_of_common_eigenvector {χ : DirichletCharacter ℂ M} {G : CuspForm (Gamma1 M) 2}
    (hG : CuspForm.IsPrimitiveForm χ G) (S : Finset ℕ) (v : CuspForm (Gamma1 M) 2) (hv0 : v ≠ 0)
    (t : ℕ → ℂ) (δ : ℕ → ℂ)
    (hvT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), CuspForm.heckeTLinOne 2 hℓ hℓM v = t ℓ • v)
    (hvD : ∀ d : ℕ, Nat.Coprime d M → CuspForm.diamondLinOne M 2 d v = δ d • v)
    (ht : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → t ℓ = qCoeff (⇑G) ℓ)
    (hδ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → δ ℓ = χ (ℓ : ZMod M))
    (O : Module.End ℂ (CuspForm (Gamma1 M) 2)) (τ a : ℂ) (hOv : O v = τ • v) (hOG : O G = a • G) :
    τ = a := by

  have hrel : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ m : ℕ,
      qCoeff (⇑v) (ℓ * m) + (ℓ * δ ℓ) * (if ℓ ∣ m then qCoeff (⇑v) (m / ℓ) else 0)
        = t ℓ * qCoeff (⇑v) m := by
    intro ℓ hℓ hℓM m
    have h := congrArg (fun F : CuspForm (Gamma1 M) 2 => qCoeff (⇑F) m) (hvT ℓ hℓ hℓM)
    rw [CuspForm.qCoeff_heckeTLinOne 2 hℓ hℓM v m, hvD ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM),
      qCoeff_smul, qCoeff_smul] at h
    rw [← h]
    have e : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [e, zpow_one]
    split_ifs <;> ring

  obtain ⟨χv, hχv, hχval⟩ := CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen M 2 v hv0
    (fun ℓ => ℓ * δ ℓ) (fun ℓ hℓ hℓM => ⟨t ℓ, fun m => hrel ℓ hℓ hℓM m⟩)
  have hχvℓ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → χv (ℓ : ZMod M) = δ ℓ := by
    intro ℓ hℓ hℓM
    have h := hχval ℓ hℓ hℓM
    have e : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [e, zpow_one, mul_comm] at h
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hℓ.ne_zero) h
  have hχeq : χv = χ := dirichlet_ext S (fun ℓ hℓ hℓM hℓS => by rw [hχvℓ ℓ hℓ hℓM, hδ ℓ hℓ hℓM hℓS])
  rw [hχeq] at hχv

  have hmult := CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M 2 χ G hG v hχv S
    (fun ℓ hℓ hℓS hℓM m => by
      have h := hrel ℓ hℓ hℓM m
      have e : ((2 : ℤ) - 1) = 1 := by norm_num
      rw [e, zpow_one, ← hδ ℓ hℓ hℓM hℓS, ← ht ℓ hℓ hℓM hℓS]
      linear_combination h)

  set c₁ := qCoeff (⇑v) 1 with hc₁
  have hc₁0 : c₁ ≠ 0 := by
    intro h0
    apply hv0
    rw [hmult, h0, zero_smul]
  have hG0 : G ≠ 0 := ne_zero_of_qCoeff_one G hG.isEigenformWith.qCoeff_one
  have h1 : O v = (c₁ * a) • G := by rw [hmult, map_smul, hOG, smul_smul]
  have h2 : O v = (τ * c₁) • G := by rw [hOv, hmult, smul_smul]
  have h3 : (c₁ * a - τ * c₁) • G = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
  have h4 : c₁ * a - τ * c₁ = 0 := by
    by_contra hne
    exact hG0 ((smul_eq_zero.1 h3).resolve_left hne)
  have h5 : c₁ * (a - τ) = 0 := by linear_combination h4
  have h6 : a - τ = 0 := (mul_eq_zero.1 h5).resolve_left hc₁0
  linear_combination -h6

end Cusp

section Device

theorem map_ne_zero_of_isIntegral {R B : Type} [CommRing R] [IsDomain R] [Ring B] [CharZero B]
    (f : R →+* B) {x : R} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : f x ≠ 0 := by
  classical
  obtain ⟨P, hPm, hP⟩ := hx
  have hP0 : P ≠ 0 := hPm.ne_zero
  obtain ⟨Q, hPQ, hQ⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 0
  rw [map_zero, sub_zero] at hPQ hQ
  have hQ0 : Q.coeff 0 ≠ 0 := fun h => hQ (Polynomial.X_dvd_iff.2 h)

  have hQx : Polynomial.aeval x Q = 0 := by
    have h : Polynomial.aeval x P = 0 := hP
    rw [hPQ, map_mul, map_pow, Polynomial.aeval_X] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ h0)
  intro hfx
  have h1 : Polynomial.aeval (f x) Q = 0 := by
    have e1 : Polynomial.aeval (f x) Q = f (Polynomial.aeval x Q) :=
      Polynomial.aeval_algHom_apply f.toIntAlgHom x Q
    rw [e1, hQx, map_zero]
  rw [hfx, Polynomial.aeval_def, Polynomial.eval₂_at_zero, eq_intCast, Int.cast_eq_zero] at h1
  exact hQ0 h1

theorem isIntegral_of_isIntegral_map {R : Type} [CommRing R] (toC : R →+* ℂ)
    (htoC : Function.Injective toC) {x : R} (hx : IsIntegral ℤ (toC x)) : IsIntegral ℤ x := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine ⟨P, hPm, htoC ?_⟩
  rw [Polynomial.eval₂_def] at hP
  rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_def]
  have e : toC.comp (algebraMap ℤ R) = algebraMap ℤ ℂ := RingHom.ext_int _ _
  rw [e]
  exact hP

theorem isIntegral_qCoeff {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2} (hh : CuspForm.IsEigenformWith χ h) (n : ℕ) :
    IsIntegral ℤ (ModularFormClass.qCoeff h n) := by
  refine IsIntegral.of_mem_of_fg _ hh.fg_adjoin_qCoeff _ ?_
  exact Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)

theorem isIntegral_conj {z : ℂ} (hz : IsIntegral ℤ z) : IsIntegral ℤ (starRingEnd ℂ z) :=
  hz.map (starRingEnd ℂ).toIntAlgHom

end Device

section Main

p2m_open "ModularCurve~baseChangeHom~IsCusp CongruenceSubgroup ModularFormClass"
open scoped MatrixGroups ModularForm ComplexConjugate

abbrev Idx (M : ℕ) : Type := Nat.Primes ⊕ {d : ℕ // Nat.Coprime d M}

def vIdx (M : ℕ) : Idx M → Nat.Primes ⊕ ℕ := Sum.map id Subtype.val

@[scoped simp] theorem vIdx_inl (M : ℕ) (ℓ : Nat.Primes) : vIdx M (Sum.inl ℓ) = Sum.inl ℓ := rfl
@[scoped simp] theorem vIdx_inr (M : ℕ) (d : {d : ℕ // Nat.Coprime d M}) : vIdx M (Sum.inr d) = Sum.inr d.1 := rfl

theorem rationalHeckeRepOne_eq_zero_of_mem (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]
    [Module HeckeAlgOne J] {t : HeckeAlgOne} (ht : t ∈ Module.annihilator HeckeAlgOne J) :
    rationalHeckeRepOne p J t = 0 := by
  have h0 : tateHeckeRepOne p J t = 0 := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [coe_tateHeckeRepOne_apply_apply, LinearMap.zero_apply, TateModule.coe_zero, Pi.zero_apply]
    exact Module.mem_annihilator.1 ht _
  rw [rationalHeckeRepOne_apply, h0, LinearMap.baseChange_zero]

section PartA

p2m_open "ModularCurve~baseChangeHom~IsCusp"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem coeigen_character
    (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] [Module.Finite K V]
    (τ : HeckeAlgOne →+* Module.End K V)
    (S : Finset ℕ) (M : ℕ) (R : Type) [CommRing R] (ψ : R →+* K) (b e : ℕ → R)
    (he0 : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → ψ (e ℓ) ≠ 0)
    (W : Type) [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    (hf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S → ∀ z : V,
          ψ (e ℓ) • f (τ (heckeGenOne ⟨ℓ, hℓ⟩) z) = ψ (b ℓ) • f z ∧
          ψ (e ℓ) • f (τ (diamondGen ℓ) z) = f z)
    (hf0 : f ≠ 0) :
    ∃ μ' : HeckeAlgOne →+* AlgebraicClosure K,
      (∀ t : HeckeAlgOne, τ t = 0 → μ' t = 0) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        μ' (heckeGenOne ⟨ℓ, hℓ⟩) * algebraMap K (AlgebraicClosure K) (ψ (e ℓ)) =
            algebraMap K (AlgebraicClosure K) (ψ (b ℓ)) ∧
        μ' (diamondGen ℓ) * algebraMap K (AlgebraicClosure K) (ψ (e ℓ)) = 1 := by
  classical
  have hτcomm : ∀ s t, τ s * τ t = τ t * τ s := fun s t => by rw [← map_mul, ← map_mul, mul_comm]

  let G : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S}
  let Aop : G → Module.End K V := fun ℓ => ψ (e ℓ.1) • τ (heckeGenOne ⟨ℓ.1, ℓ.2.1⟩) - ψ (b ℓ.1) • 1
  let Bop : G → Module.End K V := fun ℓ => ψ (e ℓ.1) • τ (diamondGen ℓ.1) - 1
  let W' : Submodule K V := ⨆ ℓ : G, LinearMap.range (Aop ℓ) ⊔ LinearMap.range (Bop ℓ)

  have hAf : ∀ ℓ : G, f ∘ₗ Aop ℓ = 0 := by
    intro ℓ
    apply LinearMap.ext
    intro z
    have h := (hf ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2 z).1
    simp only [Aop, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, LinearMap.zero_apply]
    rw [h, sub_self]
  have hBf : ∀ ℓ : G, f ∘ₗ Bop ℓ = 0 := by
    intro ℓ
    apply LinearMap.ext
    intro z
    have h := (hf ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2 z).2
    simp only [Bop, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, LinearMap.zero_apply]
    rw [h, sub_self]
  have hW'f : W' ≤ LinearMap.ker f := by
    refine iSup_le fun ℓ => sup_le ?_ ?_
    · exact LinearMap.range_le_ker_iff.2 (hAf ℓ)
    · exact LinearMap.range_le_ker_iff.2 (hBf ℓ)
  have hW'top : W' ≠ ⊤ := by
    intro htop
    apply hf0
    apply LinearMap.ext
    intro z
    have hz : z ∈ W' := by rw [htop]; exact Submodule.mem_top
    exact LinearMap.mem_ker.1 (hW'f hz)

  have hinv : ∀ t : HeckeAlgOne, ∀ w ∈ W', τ t w ∈ W' := by
    intro t
    have hle : W'.map (τ t) ≤ W' := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun ℓ => ?_
      rw [Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp]
      have hA : τ t ∘ₗ Aop ℓ = Aop ℓ ∘ₗ τ t := by
        show τ t * Aop ℓ = Aop ℓ * τ t
        simp only [Aop, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
        rw [hτcomm]
      have hB : τ t ∘ₗ Bop ℓ = Bop ℓ ∘ₗ τ t := by
        show τ t * Bop ℓ = Bop ℓ * τ t
        simp only [Bop, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
        rw [hτcomm]
      rw [hA, hB]
      exact sup_le_sup (LinearMap.range_comp_le_range _ _) (LinearMap.range_comp_le_range _ _)
    intro w hw
    exact hle (Submodule.mem_map_of_mem hw)

  haveI : Nontrivial (V ⧸ W') := (Submodule.Quotient.nontrivial_iff (p := W')).2 hW'top
  let τq : HeckeAlgOne →+* Module.End K (V ⧸ W') :=
    { toFun := fun t => W'.mapQ W' (τ t) (fun w hw => hinv t w hw)
      map_one' := by
        apply Submodule.linearMap_qext
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, map_one,
          Module.End.one_apply]
      map_mul' := fun s t => by
        apply Submodule.linearMap_qext
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, map_mul,
          Module.End.mul_apply]
      map_zero' := by
        apply Submodule.linearMap_qext
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, map_zero,
          LinearMap.zero_apply, Submodule.Quotient.mk_zero]
      map_add' := fun s t => by
        apply Submodule.linearMap_qext
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, map_add,
          LinearMap.add_apply, Submodule.Quotient.mk_add] }
  have hτq : ∀ (t : HeckeAlgOne) (z : V), τq t (Submodule.Quotient.mk z) = Submodule.Quotient.mk (τ t z) :=
    fun _ _ => rfl

  have hAq : ∀ ℓ : G, ψ (e ℓ.1) • τq (heckeGenOne ⟨ℓ.1, ℓ.2.1⟩) = ψ (b ℓ.1) • 1 := by
    intro ℓ
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hτq, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact (le_iSup (fun ℓ : G => LinearMap.range (Aop ℓ) ⊔ LinearMap.range (Bop ℓ)) ℓ)
      (Submodule.mem_sup_left (LinearMap.mem_range_self (Aop ℓ) z))
  have hBq : ∀ ℓ : G, ψ (e ℓ.1) • τq (diamondGen ℓ.1) = 1 := by
    intro ℓ
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hτq, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact (le_iSup (fun ℓ : G => LinearMap.range (Aop ℓ) ⊔ LinearMap.range (Bop ℓ)) ℓ)
      (Submodule.mem_sup_right (LinearMap.mem_range_self (Bop ℓ) z))

  let C : Subalgebra K (Module.End K (V ⧸ W')) := Algebra.adjoin K (Set.range τq)
  letI : CommRing C := Algebra.adjoinCommRingOfComm K (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    show τq s * τq t = τq t * τq s
    rw [← map_mul, ← map_mul, mul_comm])
  haveI : Nontrivial C := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal C
  haveI : 𝔪.IsMaximal := h𝔪
  haveI : Module.Finite K C := Module.Finite.of_injective (Subalgebra.toSubmodule C).subtype Subtype.val_injective
  haveI : Module.Finite K (C ⧸ 𝔪) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔪).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic K (C ⧸ 𝔪) := Algebra.IsAlgebraic.of_finite K (C ⧸ 𝔪)
  letI : Field (C ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let θ : C →ₐ[K] AlgebraicClosure K :=
    (IsAlgClosed.lift : (C ⧸ 𝔪) →ₐ[K] AlgebraicClosure K).comp (Ideal.Quotient.mkₐ K 𝔪)
  have hτqmem : ∀ t, τq t ∈ C := fun t => Algebra.subset_adjoin (Set.mem_range_self t)
  let τqC : HeckeAlgOne →+* C := τq.codRestrict C hτqmem
  have hτqC : ∀ t, (τqC t : Module.End K (V ⧸ W')) = τq t := fun _ => rfl
  let μ' : HeckeAlgOne →+* AlgebraicClosure K := (θ : C →+* AlgebraicClosure K).comp τqC
  have hμ' : ∀ t, μ' t = θ (τqC t) := fun _ => rfl
  refine ⟨μ', ?_, ?_⟩
  · intro t ht
    have h3 : τq t = 0 := by
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro z
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
      rw [hτq, ht, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
    have h4 : τqC t = 0 := Subtype.ext (by rw [hτqC, h3]; rfl)
    rw [hμ', h4, map_zero]
  · intro ℓ hℓ hℓM hℓS
    let ℓ' : G := ⟨ℓ, hℓ, hℓM, hℓS⟩
    have hA : ψ (e ℓ) • τqC (heckeGenOne ⟨ℓ, hℓ⟩) = ψ (b ℓ) • (1 : C) := by
      apply Subtype.ext
      rw [SetLike.val_smul, SetLike.val_smul, hτqC, OneMemClass.coe_one]
      exact hAq ℓ'
    have hB : ψ (e ℓ) • τqC (diamondGen ℓ) = (1 : C) := by
      apply Subtype.ext
      rw [SetLike.val_smul, hτqC, OneMemClass.coe_one]
      exact hBq ℓ'
    refine ⟨?_, ?_⟩
    · have h := congrArg θ hA
      rw [map_smul, map_smul, map_one, Algebra.smul_def, Algebra.smul_def, mul_one] at h
      rw [hμ', mul_comm]
      exact h
    · have h := congrArg θ hB
      rw [map_smul, map_one, Algebra.smul_def] at h
      rw [hμ', mul_comm]
      exact h

end PartA

set_option maxHeartbeats 160000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open scoped IsMulCommutative in

theorem engine
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (N : ℕ) [NeZero N] (hNM : N ∣ M)
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hcomm : ModularCurve.HeckeDiamondCommuteBar N)
    (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* Ω)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (μ' : HeckeAlgOne →+* Ω)
    (hK0' : ∀ t : HeckeAlgOne, heckeEvalOneBar hcomm t = 0 → μ' t = 0)
    (hμv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        μ' (heckeGenOne ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧ μ' (diamondGen ℓ) * ψ (e ℓ) = 1) :
    ∃ (v : CuspForm (Gamma1 N) 2) (aT dD : ℕ → ℂ), v ≠ 0 ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N), CuspForm.heckeTLinOne 2 hq hqN v = aT q • v) ∧
      (∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = dD d • v) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → aT ℓ = qCoeff (⇑g) ℓ * (ε (ℓ : ZMod M))⁻¹) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → dD ℓ = (ε (ℓ : ZMod M))⁻¹) := by
  classical

  haveI : NoZeroDivisors R := htoC.noZeroDivisors toC (map_zero toC) (map_mul toC)
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => by
    have h' := congrArg toC h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'⟩⟩
  haveI : IsDomain R := NoZeroDivisors.to_isDomain R
  haveI : CharZero R := ⟨fun a a' haa => by
    have h := congrArg toC haa
    simp only [map_natCast] at h
    exact Nat.cast_injective h⟩

  obtain ⟨Φ, hΦinj, hΦT, hΦD, hΦU⟩ :=
    exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff N hin hcomm
  obtain ⟨rn, hrn⟩ : ∃ rn : MvPolynomial (Idx N) ℤ →+* HeckeAlgOne,
      ∀ i, rn (MvPolynomial.X i) = MvPolynomial.X (vIdx N i) :=
    ⟨MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlgOne) (fun i => MvPolynomial.X (vIdx N i)),
      fun i => MvPolynomial.eval₂_X _ _ _⟩
  obtain ⟨Φz, hΦzdef⟩ : ∃ Φz : MvPolynomial (Idx N) ℤ →+* Module.End ℂ (CuspForm (Gamma1 N) 2),
      ∀ P, Φz P = Φ (heckeEvalOneBarAux hcomm (rn P)) :=
    ⟨Φ.comp ((heckeEvalOneBarAux hcomm).toRingHom.comp rn), fun _ => rfl⟩
  have hΦzT : ∀ (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N),
      Φz (MvPolynomial.X (Sum.inl ℓ)) = CuspForm.heckeTLinOne 2 ℓ.prop hℓN := by
    intro ℓ hℓN
    rw [hΦzdef, hrn]
    show Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inl ℓ))) = _
    rw [heckeEvalOneBarAux_X]
    have e0 : (⟨heckeDiamondGenBar N (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar N))))
        = ⟨heckeOperatorOneBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inl N ℓ)
    rw [e0, hΦT ℓ hℓN]
  have hΦzD : ∀ d : {d : ℕ // Nat.Coprime d N},
      Φz (MvPolynomial.X (Sum.inr d)) = CuspForm.diamondLinOne N 2 d := by
    intro d
    rw [hΦzdef, hrn]
    show Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inr (d : ℕ)))) = _
    rw [heckeEvalOneBarAux_X]
    have e0 : (⟨heckeDiamondGenBar N (Sum.inr (d : ℕ)), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar N))))
        = ⟨diamondOneBar N d, Algebra.subset_adjoin (Set.mem_range_self (Sum.inr (d : ℕ)))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inr N d)
    rw [e0, hΦD d.1 d.2]
  have hΦzU : ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ∣ N → ∀ (f : CuspForm (Gamma1 N) 2) (m : ℕ),
      qCoeff (⇑(Φz (MvPolynomial.X (Sum.inl ℓ)) f)) m = qCoeff (⇑f) (ℓ * m) := by
    intro ℓ hℓN f m
    rw [hΦzdef, hrn]
    show qCoeff (⇑(Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inl ℓ))) f)) m = _
    rw [heckeEvalOneBarAux_X]
    have e0 : (⟨heckeDiamondGenBar N (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar N))))
        = ⟨heckeOperatorOneBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inl N ℓ)
    rw [e0]
    exact hΦU ℓ hℓN f m

  obtain ⟨μ, hμdef⟩ : ∃ μ : MvPolynomial (Idx N) ℤ →+* Ω, ∀ P, μ P = μ' (rn P) :=
    ⟨μ'.comp rn, fun _ => rfl⟩
  have hμT : ∀ ℓ : Nat.Primes, μ (MvPolynomial.X (Sum.inl ℓ)) = μ' (heckeGenOne ℓ) := by
    intro ℓ
    rw [hμdef, hrn]
    rfl
  have hμD : ∀ d : {d : ℕ // Nat.Coprime d N},
      μ (MvPolynomial.X (Sum.inr d)) = μ' (diamondGen d.1) := by
    intro d
    rw [hμdef, hrn]
    rfl
  have hK0 : ∀ P : MvPolynomial (Idx N) ℤ, Φz P = 0 → μ P = 0 := by
    intro P hP
    rw [hΦzdef] at hP
    have h1 : heckeEvalOneBarAux hcomm (rn P) = 0 := hΦinj (by rw [map_zero]; exact hP)
    have h2 : heckeEvalOneBar hcomm (rn P) = 0 := by
      rw [heckeEvalOneBar_apply, h1]; rfl
    rw [hμdef]
    exact hK0' _ h2

  obtain ⟨n, bs, hbs⟩ := CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast N 2
  haveI : FiniteDimensional ℂ (CuspForm (Gamma1 N) 2) := Module.Finite.of_basis bs
  have hbsQ : ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ m : ℕ,
      qCoeff ((⇑(bs i) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) m ∈ Set.range (algebraMap ℚ ℂ) := by
    intro i γ hγ m
    obtain ⟨z, hz⟩ := hbs i γ hγ m
    exact ⟨z, by rw [← hz]; simp⟩
  have hbs1 : ∀ (i : Fin n) (m : ℕ), qCoeff (⇑(bs i)) m ∈ Set.range (algebraMap ℚ ℂ) := by
    intro i m
    have h := hbsQ i 1 (Subgroup.one_mem _) m
    rwa [SlashAction.slash_one] at h
  have hdiaQ : ∀ (i : Fin n) {dd : ℕ} (hdd : Nat.Coprime dd N) (m : ℕ),
      qCoeff (⇑(CuspForm.diamondLinOne N 2 dd (bs i))) m ∈ Set.range (algebraMap ℚ ℂ) := by
    intro i dd hdd m
    obtain ⟨γ, hγ⟩ := CuspForm.exists_isDiamondLift_of_coprime hdd
    rw [CuspForm.coe_diamondLinOne_apply hγ]
    exact hbsQ i γ hγ.1 m
  have hrat : ∀ i, RatOp bs (Φz (MvPolynomial.X i)) := by
    rintro (ℓ | ⟨dd, hdd⟩)
    · by_cases hℓN : (ℓ : ℕ) ∣ N
      · intro j k
        exact repr_rational_of_qCoeff_rational bs hbs1 _
          (fun m => by rw [hΦzU ℓ hℓN]; exact hbs1 j _) k
      · intro j k
        refine repr_rational_of_qCoeff_rational bs hbs1 _ (fun m => ?_) k
        obtain ⟨q1, h1⟩ := hbs1 j (ℓ * m)
        obtain ⟨q2, h2⟩ := hdiaQ j ((Nat.Prime.coprime_iff_not_dvd ℓ.prop).2 hℓN) (m / ℓ)
        refine ⟨q1 + (ℓ : ℚ) * (if (ℓ : ℕ) ∣ m then q2 else 0), ?_⟩
        have e2 : ((2 : ℤ) - 1) = 1 := by norm_num
        rw [hΦzT ℓ hℓN, CuspForm.qCoeff_heckeTLinOne, e2, zpow_one, ← h1]
        split_ifs with hdiv
        · rw [← h2]; simp
        · simp
    · intro j k
      refine repr_rational_of_qCoeff_rational bs hbs1 _ (fun m => ?_) k
      rw [hΦzD]
      exact hdiaQ j hdd m

  have halg : ∀ i, IsAlgebraic ℚ (μ (MvPolynomial.X i)) :=
    fun i => isAlgebraic_of_relations bs Φz hrat μ hK0 i

  let G₀ : Set R :=
    (Set.range fun ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S} => b ℓ.1) ∪
      (Set.range fun ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S} => e ℓ.1)
  have hbint : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsIntegral ℤ (b ℓ) := fun ℓ hℓ hℓM hℓS =>
    isIntegral_of_isIntegral_map toC htoC (by rw [hb ℓ hℓ hℓM hℓS]; exact isIntegral_qCoeff hg.isEigenformWith ℓ)
  have heint : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsIntegral ℤ (e ℓ) := fun ℓ hℓ hℓM hℓS =>
    isIntegral_of_isIntegral_map toC htoC (by
      rw [he ℓ hℓ hℓM hℓS]
      refine IsIntegral.of_pow (Nat.totient_pos.2 (NeZero.pos M)) ?_
      rw [dirichlet_pow_totient ε ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)]
      exact isIntegral_one)
  have hG₀int : ∀ x ∈ G₀, IsIntegral ℤ x := by
    rintro x (⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩ | ⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩)
    · exact hbint ℓ hℓ hℓM hℓS
    · exact heint ℓ hℓ hℓM hℓS
  let R₀ : Subalgebra ℤ R := Algebra.adjoin ℤ G₀
  have hR₀int : ∀ x ∈ R₀, IsIntegral ℤ x := fun x hx => by
    have hle : R₀ ≤ integralClosure ℤ R :=
      Algebra.adjoin_le fun y hy => (mem_integralClosure_iff ℤ R).2 (hG₀int y hy)
    exact (mem_integralClosure_iff ℤ R).1 (hle hx)
  have hbmem : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → b ℓ ∈ R₀ := fun ℓ hℓ hℓM hℓS =>
    Algebra.subset_adjoin (Or.inl ⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩)
  have hemem : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → e ℓ ∈ R₀ := fun ℓ hℓ hℓM hℓS =>
    Algebra.subset_adjoin (Or.inr ⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩)
  have hψinj : Function.Injective (ψ.comp R₀.val.toRingHom) := by
    intro x y hxy
    by_contra hne
    have hne' : (x : R) - y ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h)
    have hint : IsIntegral ℤ ((x : R) - y) := hR₀int _ (R₀.sub_mem x.2 y.2)
    apply map_ne_zero_of_isIntegral ψ hint hne'
    have : ψ x = ψ y := hxy
    rw [map_sub, this, sub_self]
  have htoCinj : Function.Injective (toC.comp R₀.val.toRingHom) := htoC.comp Subtype.val_injective
  let K₀ : Type := FractionRing R₀
  haveI : CharZero K₀ := charZero_of_injective_algebraMap (IsFractionRing.injective R₀ K₀)
  letI algΩ : Algebra K₀ Ω := (IsFractionRing.lift hψinj : K₀ →+* Ω).toAlgebra
  letI algC : Algebra K₀ ℂ := (IsFractionRing.lift htoCinj : K₀ →+* ℂ).toAlgebra
  have hjΩ : ∀ x : R₀, algebraMap K₀ Ω (algebraMap R₀ K₀ x) = ψ x := fun x =>
    IsFractionRing.lift_algebraMap hψinj x
  have hjC : ∀ x : R₀, algebraMap K₀ ℂ (algebraMap R₀ K₀ x) = toC x := fun x =>
    IsFractionRing.lift_algebraMap htoCinj x
  haveI : IsScalarTower ℚ K₀ Ω := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ K₀), map_ratCast]
  let F₁ : IntermediateField K₀ Ω :=
    IntermediateField.adjoin K₀ (Set.range fun i : Idx N => μ (MvPolynomial.X i))
  haveI : Algebra.IsAlgebraic K₀ F₁ := IntermediateField.isAlgebraic_adjoin fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact ((halg i).tower_top K₀).isIntegral
  let ιE : F₁ →ₐ[K₀] ℂ := IsAlgClosed.lift
  have hμmem : ∀ P : MvPolynomial (Idx N) ℤ, μ P ∈ F₁ := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => rw [eq_intCast MvPolynomial.C, map_intCast]; exact intCast_mem F₁ a
    | add f f' hf hf' => rw [map_add]; exact add_mem hf hf'
    | mul_X f i hf =>
      rw [map_mul]
      exact mul_mem hf (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
  obtain ⟨μc, hμc⟩ : ∃ μc : MvPolynomial (Idx N) ℤ →+* ℂ, ∀ P, μc P = ιE ⟨μ P, hμmem P⟩ :=
    ⟨(ιE : F₁ →+* ℂ).comp (μ.codRestrict F₁ hμmem), fun _ => rfl⟩
  have hK0c : ∀ P : MvPolynomial (Idx N) ℤ, Φz P = 0 → μc P = 0 := by
    intro P hP
    rw [hμc]
    have h0 : (⟨μ P, hμmem P⟩ : F₁) = 0 := Subtype.ext (hK0 P hP)
    rw [h0, map_zero]
  have hψmem : ∀ x : R₀, ψ x ∈ F₁ := fun x => by
    rw [← hjΩ]; exact IntermediateField.algebraMap_mem F₁ _
  have hιψ : ∀ x : R₀, ιE ⟨ψ x, hψmem x⟩ = toC x := by
    intro x
    have e1 : (⟨ψ x, hψmem x⟩ : F₁) = algebraMap K₀ F₁ (algebraMap R₀ K₀ x) :=
      Subtype.ext (hjΩ x).symm
    rw [e1, AlgHom.commutes, hjC]

  have hval : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S →
      μc (MvPolynomial.X (Sum.inl ⟨ℓ, hℓ⟩)) = qCoeff (⇑g) ℓ * (ε (ℓ : ZMod M))⁻¹ ∧
      μc (MvPolynomial.X (Sum.inr ⟨ℓ, (Nat.Prime.coprime_iff_not_dvd hℓ).2
        (fun h => hℓM (dvd_trans h hNM))⟩)) = (ε (ℓ : ZMod M))⁻¹ := by
    intro ℓ hℓ hℓM hℓS
    have hcopM : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM
    have hcop : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).2 (fun h => hℓM (dvd_trans h hNM))
    obtain ⟨hΛT, hΛD⟩ := hμv ℓ hℓ hℓM hℓS
    have hεℓ : ε (ℓ : ZMod M) ≠ 0 := dirichlet_ne_zero ε hcopM

    have hTF : (⟨μ (MvPolynomial.X (Sum.inl ⟨ℓ, hℓ⟩)), hμmem _⟩ : F₁) * ⟨ψ (e ℓ), hψmem ⟨e ℓ, hemem ℓ hℓ hℓM hℓS⟩⟩
        = ⟨ψ (b ℓ), hψmem ⟨b ℓ, hbmem ℓ hℓ hℓM hℓS⟩⟩ := by
      apply Subtype.ext
      rw [IntermediateField.coe_mul]
      show μ (MvPolynomial.X (Sum.inl ⟨ℓ, hℓ⟩)) * ψ (e ℓ) = ψ (b ℓ)
      rw [hμT]; exact hΛT
    have hDF : (⟨μ (MvPolynomial.X (Sum.inr ⟨ℓ, hcop⟩)), hμmem _⟩ : F₁) * ⟨ψ (e ℓ), hψmem ⟨e ℓ, hemem ℓ hℓ hℓM hℓS⟩⟩
        = 1 := by
      apply Subtype.ext
      rw [IntermediateField.coe_mul, IntermediateField.coe_one]
      show μ (MvPolynomial.X (Sum.inr ⟨ℓ, hcop⟩)) * ψ (e ℓ) = 1
      rw [hμD]; exact hΛD

    have hTC : μc (MvPolynomial.X (Sum.inl ⟨ℓ, hℓ⟩)) * ε (ℓ : ZMod M) = qCoeff (⇑g) ℓ := by
      have h := congrArg ιE hTF
      rw [map_mul, hιψ ⟨e ℓ, hemem ℓ hℓ hℓM hℓS⟩, hιψ ⟨b ℓ, hbmem ℓ hℓ hℓM hℓS⟩] at h
      rw [hμc, ← he ℓ hℓ hℓM hℓS, ← hb ℓ hℓ hℓM hℓS]
      exact h
    have hDC : μc (MvPolynomial.X (Sum.inr ⟨ℓ, hcop⟩)) * ε (ℓ : ZMod M) = 1 := by
      have h := congrArg ιE hDF
      rw [map_mul, hιψ ⟨e ℓ, hemem ℓ hℓ hℓM hℓS⟩, map_one] at h
      rw [hμc, ← he ℓ hℓ hℓM hℓS]
      exact h
    refine ⟨?_, ?_⟩
    · rw [eq_mul_inv_iff_mul_eq₀ hεℓ]
      exact hTC
    · exact eq_inv_of_mul_eq_one_left hDC

  let A₀ : Subalgebra ℂ (Module.End ℂ (CuspForm (Gamma1 N) 2)) :=
    Algebra.adjoin ℂ (Set.range fun i : Idx N => Φz (MvPolynomial.X i))
  haveI : IsMulCommutative A₀ := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    show Φz _ * Φz _ = Φz _ * Φz _
    rw [← map_mul, ← map_mul, mul_comm])
  obtain ⟨ΦC, hΦC⟩ : ∃ ΦC : MvPolynomial (Idx N) ℂ →ₐ[ℂ] Module.End ℂ (CuspForm (Gamma1 N) 2),
      ∀ i, ΦC (MvPolynomial.X i) = Φz (MvPolynomial.X i) := by
    refine ⟨A₀.val.comp (MvPolynomial.aeval fun i =>
      (⟨Φz (MvPolynomial.X i), Algebra.subset_adjoin (Set.mem_range_self i)⟩ : A₀)), fun i => ?_⟩
    show A₀.val (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    rfl
  have hKC := complexRelations bs Φz hrat ΦC hΦC μc hK0c
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector ΦC (fun i => μc (MvPolynomial.X i)) hKC

  refine ⟨v, fun q => if h : q.Prime then μc (MvPolynomial.X (Sum.inl ⟨q, h⟩)) else 0,
    fun d => if h : Nat.Coprime d N then μc (MvPolynomial.X (Sum.inr ⟨d, h⟩)) else 0, hv0, ?_, ?_, ?_, ?_⟩
  · intro q hq hqN
    dsimp only
    rw [dif_pos hq, ← hΦzT ⟨q, hq⟩ hqN, ← hΦC]
    exact hv _
  · intro d hd
    dsimp only
    rw [dif_pos hd, ← hΦzD ⟨d, hd⟩, ← hΦC]
    exact hv _
  · intro ℓ hℓ hℓM hℓS
    dsimp only
    rw [dif_pos hℓ]
    exact (hval ℓ hℓ hℓM hℓS).1
  · intro ℓ hℓ hℓM hℓS
    dsimp only
    rw [dif_pos ((Nat.Prime.coprime_iff_not_dvd hℓ).2 (fun h => hℓM (dvd_trans h hNM)))]
    exact (hval ℓ hℓ hℓM hℓS).2

set_option maxHeartbeats 6400000 in

theorem main
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (N : ℕ) [NeZero N] (hNM : N ∣ M) (hne : N ≠ M) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hcomm : ModularCurve.HeckeDiamondCommuteBar N)
    (S : Finset ℕ) (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* K)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    [Module HeckeAlgOne (JOne N)]
    (hsmul : ∀ (t : HeckeAlgOne) (x : JOne N), t • x = heckeEvalOneBar hcomm t x)
    (W : Type) [AddCommGroup W] [Module K W]
    (f : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N) →ₗ[K] W)
    (hf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        ∀ z : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N),
          ψ (e ℓ) • f ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne N)
              (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).baseChange K z) = ψ (b ℓ) • f z ∧
          ψ (e ℓ) • f ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne N)
              (ModularCurve.diamondGen ℓ)).baseChange K z) = f z) :
    f = 0 := by
  classical
  by_contra hf0

  haveI : NoZeroDivisors R := htoC.noZeroDivisors toC (map_zero toC) (map_mul toC)
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => by
    have h' := congrArg toC h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'⟩⟩
  haveI : IsDomain R := NoZeroDivisors.to_isDomain R
  have he0 : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → ψ (e ℓ) ≠ 0 := by
    intro ℓ hℓ hℓM hℓS
    have hcopM : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM
    have hne0 : e ℓ ≠ 0 := fun h0 => by
      have := he ℓ hℓ hℓM hℓS
      rw [h0, map_zero] at this
      exact dirichlet_ne_zero ε hcopM this.symm
    have hint : IsIntegral ℤ (e ℓ) := isIntegral_of_isIntegral_map toC htoC (by
      rw [he ℓ hℓ hℓM hℓS]
      refine IsIntegral.of_pow (Nat.totient_pos.2 (NeZero.pos M)) ?_
      rw [dirichlet_pow_totient ε hcopM]
      exact isIntegral_one)
    exact map_ne_zero_of_isIntegral ψ hint hne0

  haveI : Module.Finite ℤ_[p] (TateModule p (JOne N)) := ModularCurve.moduleFinite_padicInt_tateModule_jOne N p
  let τ : HeckeAlgOne →+* Module.End K (K ⊗[ℤ_[p]] TateModule p (JOne N)) :=
    (Module.End.baseChangeHom ℤ_[p] K (TateModule p (JOne N))).toRingHom.comp (tateHeckeRepOne p (JOne N))
  have hτ : ∀ t, τ t = (tateHeckeRepOne p (JOne N) t).baseChange K := fun _ => rfl
  obtain ⟨μ', hK0τ, hμv⟩ := coeigen_character K (K ⊗[ℤ_[p]] TateModule p (JOne N)) τ S M R ψ b e he0 W f
    (fun ℓ hℓ hℓM hℓS z => hf ℓ hℓ hℓM hℓS z) hf0
  have hK0' : ∀ t : HeckeAlgOne, heckeEvalOneBar hcomm t = 0 → μ' t = 0 := by
    intro t ht
    apply hK0τ
    have h1 : tateHeckeRepOne p (JOne N) t = 0 := by
      refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
      rw [coe_tateHeckeRepOne_apply_apply, LinearMap.zero_apply, TateModule.coe_zero, Pi.zero_apply, hsmul, ht,
        LinearMap.zero_apply]
    rw [hτ, h1, LinearMap.baseChange_zero]

  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  obtain ⟨v, aT, dD, hv0, hT, hD, hTv, hDv⟩ :=
    engine hg N hNM hin hcomm S (AlgebraicClosure K) R toC htoC ((algebraMap K (AlgebraicClosure K)).comp ψ)
      b e hb he μ' hK0' (fun ℓ hℓ hℓM hℓS => hμv ℓ hℓ hℓM hℓS)

  exact hg.not_eigenpacketOccursAt hNM hne (_root_.E2E.ending hg N hNM S v hv0 aT dD hT hD hTv hDv)

end Main

end E2E93
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne.E2E93"

end
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne.E2E93"

p2m_open "ModularCurve~baseChangeHom~IsCusp" in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (N : ℕ) [NeZero N] (hNM : N ∣ M) (hne : N ≠ M) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hcomm : ModularCurve.HeckeDiamondCommuteBar N)
    (S : Finset ℕ) (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* K)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    letI := ModularCurve.heckeModuleOneBar N
    ∀ (W : Type) [AddCommGroup W] [Module K W]
      (f : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N) →ₗ[K] W),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        ∀ z : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N),
          ψ (e ℓ) • f ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne N)
              (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).baseChange K z) = ψ (b ℓ) • f z ∧
          ψ (e ℓ) • f ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne N)
              (ModularCurve.diamondGen ℓ)).baseChange K z) = f z) →
      f = 0 := by
  letI := ModularCurve.heckeModuleOneBar N
  intro W _ _ f hf
  exact E2E93.main hg N hNM hne p hin hcomm S K R toC htoC ψ b e hb he
    (fun t x => ModularCurve.heckeModuleOneBar_smul_def hcomm t x) W f hf

end S_CuspForm_IsPrimitiveForm_linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_linearMap_eq_zero_of_hecke_coeigen_tateModule_jOne_of_dvd_of_ne (solution)
