-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5ae55945-b049-52a2-b023-e7e0660fdc26

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Theorems.Thm_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne
import Theorems.Thm_CuspForm_qCoeff_diamondLinOne_two_mem_range_ratCast_of_qCoeff_mem_range_intCast
import Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff
import Theorems.Thm_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast
import Theorems.Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul
import Theorems.Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace C2aII

p2m_open "ModularCurve~IsCusp"

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

theorem cusp_analytic (F : CuspForm (Γ₁ℝ M) k) : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)

theorem cusp_ext_of_qCoeff {F G : CuspForm (Γ₁ℝ M) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem qCoeff_smul (c : ℂ) (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (cusp_analytic F) c, map_smul, smul_eq_mul]

theorem qCoeff_add (F G : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(F + G)) n = qCoeff (⇑F) n + qCoeff (⇑G) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_add, qExpansion_add (cusp_analytic F) (cusp_analytic G),
    map_add]

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ M) k)) n = 0 := by
  rw [qCoeff, CuspForm.coe_zero, qExpansion_zero, map_zero]

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (F : ι → CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, F i)) n = ∑ i ∈ s, qCoeff (⇑(F i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qCoeff_zero']
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, qCoeff_add, ih]

theorem ne_zero_of_qCoeff_one (F : CuspForm (Γ₁ℝ M) k) (h1 : qCoeff (⇑F) 1 = 1) : F ≠ 0 := by
  rintro rfl
  rw [qCoeff_zero'] at h1
  exact zero_ne_one h1

end QExp

section RatForm

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

variable (M : ℕ) (k : ℤ)

local notation "V" => CuspForm (Gamma1 M) k

def ratModule : Module ℚ V := Module.compHom _ (algebraMap ℚ ℂ)

attribute [local instance] ratModule

theorem rat_smul_def (q : ℚ) (f : V) : q • f = (q : ℂ) • f := rfl

scoped instance ratTower : IsScalarTower ℚ ℂ V :=
  ⟨fun q c f => by rw [rat_smul_def, smul_smul, Rat.smul_def]⟩

def IsRat (f : V) : Prop := ∀ n : ℕ, ∃ q : ℚ, (q : ℂ) = qCoeff (⇑f) n

def VQ : Submodule ℚ V where
  carrier := {f | IsRat M k f}
  add_mem' {f g} hf hg n := by
    obtain ⟨a, ha⟩ := hf n; obtain ⟨b, hb⟩ := hg n
    exact ⟨a + b, by rw [Rat.cast_add, ha, hb, qCoeff_add]⟩
  zero_mem' n := ⟨0, by rw [Rat.cast_zero, qCoeff_zero']⟩
  smul_mem' q f hf n := by
    obtain ⟨a, ha⟩ := hf n
    refine ⟨q * a, ?_⟩
    show ((q * a : ℚ) : ℂ) = qCoeff (⇑(((q : ℂ) • f : V))) n
    rw [Rat.cast_mul, ha, qCoeff_smul]

variable {M k}

theorem mem_VQ {f : V} : f ∈ VQ M k ↔ IsRat M k f := Iff.rfl

theorem mem_VQ_of_int {f : V} (hf : ∀ n : ℕ, qCoeff (⇑f) n ∈ Set.range ((↑) : ℤ → ℂ)) : f ∈ VQ M k := by
  intro n
  obtain ⟨z, hz⟩ := hf n
  exact ⟨z, by rw [Rat.cast_intCast, hz]⟩

theorem mem_VQ_of_rat {f : V} (hf : ∀ n : ℕ, qCoeff (⇑f) n ∈ Set.range ((↑) : ℚ → ℂ)) : f ∈ VQ M k :=
  fun n => hf n

theorem hli (n : ℕ) (v : Fin n → V) (hv : ∀ i, v i ∈ VQ M k) (hind : LinearIndependent ℚ v) :
    LinearIndependent ℂ v := by
  classical
  by_contra hdep
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep

  choose a ha using fun i => hv i

  let W : Submodule ℚ ℂ := Submodule.span ℚ (Set.range c)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range c)
  let bW := Module.finBasis ℚ W
  let cW : Fin n → W := fun i => ⟨c i, Submodule.subset_span ⟨i, rfl⟩⟩
  let r : Fin n → Fin (Module.finrank ℚ W) → ℚ := fun i j => bW.repr (cW i) j
  have hcr : ∀ i, c i = ∑ j, (r i j : ℂ) * (bW j : ℂ) := by
    intro i
    have h1 : (cW i : ℂ) = ((∑ j, bW.repr (cW i) j • bW j : W) : ℂ) := by rw [bW.sum_repr]
    rw [show c i = (cW i : ℂ) from rfl, h1, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Rat.smul_def]

  have hbW : LinearIndependent ℚ (fun j => (bW j : ℂ)) := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)

  have hrel : ∀ (m : ℕ) (j), ∑ i, r i j * a i m = 0 := by
    intro m
    have h1 : ∑ i, c i * qCoeff (⇑(v i)) m = 0 := by
      have := congrArg (fun F : V => qCoeff (⇑F) m) hc
      try simp only at this
      rw [qCoeff_sum, qCoeff_zero'] at this
      simpa only [qCoeff_smul] using this
    have h2 : ∑ j, (∑ i, r i j * a i m) • (bW j : ℂ) = 0 := by
      calc ∑ j, (∑ i, r i j * a i m) • (bW j : ℂ)
          = ∑ j, ∑ i, ((r i j : ℂ) * (a i m : ℂ)) * (bW j : ℂ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Rat.smul_def, Rat.cast_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Rat.cast_mul]
        _ = ∑ i, (a i m : ℂ) * ∑ j, (r i j : ℂ) * (bW j : ℂ) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ i, c i * qCoeff (⇑(v i)) m := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← hcr i, ha i m, mul_comm]
        _ = 0 := h1
    exact Fintype.linearIndependent_iff.1 hbW (fun j => ∑ i, r i j * a i m) h2

  have hr0 : ∀ i j, r i j = 0 := by
    intro i j
    have h1 : ∑ i, r i j • v i = 0 := by
      refine cusp_ext_of_qCoeff fun m => ?_
      rw [qCoeff_sum, qCoeff_zero']
      simp_rw [rat_smul_def, qCoeff_smul, ← ha]
      have := hrel m j
      exact_mod_cast this
    exact Fintype.linearIndependent_iff.1 hind (fun i => r i j) h1 i
  apply hi₀
  rw [hcr i₀]
  simp [hr0]

end RatForm

section Diamond

open CongruenceSubgroup ModularFormClass UpperHalfPlane
open scoped MatrixGroups ModularForm

variable {M : ℕ} {k : ℤ}

theorem diamondLinOne_congr {d d' : ℕ} (h : (d : ZMod M) = (d' : ZMod M)) :
    CuspForm.diamondLinOne M k d = CuspForm.diamondLinOne M k d' := by
  by_cases hd : ∃ γ : SL(2, ℤ), CuspForm.IsDiamondLift M d γ
  · obtain ⟨γ, hγ⟩ := hd
    have hγ' : CuspForm.IsDiamondLift M d' γ := ⟨hγ.1, hγ.2.trans h⟩
    refine LinearMap.ext fun f => DFunLike.ext' ?_
    rw [CuspForm.coe_diamondLinOne_apply hγ, CuspForm.coe_diamondLinOne_apply hγ']
  · have hd' : ¬ ∃ γ : SL(2, ℤ), CuspForm.IsDiamondLift M d' γ := fun ⟨γ, hγ⟩ =>
      hd ⟨γ, hγ.1, hγ.2.trans h.symm⟩
    rw [CuspForm.diamondLinOne_of_not hd, CuspForm.diamondLinOne_of_not hd']

theorem diamondLinOne_mul {a b : ℕ} (ha : Nat.Coprime a M) (hb : Nat.Coprime b M) :
    CuspForm.diamondLinOne M k a * CuspForm.diamondLinOne M k b = CuspForm.diamondLinOne M k (a * b) := by
  obtain ⟨γa, hγa⟩ := CuspForm.exists_isDiamondLift_of_coprime (M := M) ha
  obtain ⟨γb, hγb⟩ := CuspForm.exists_isDiamondLift_of_coprime (M := M) hb
  have hγ : CuspForm.IsDiamondLift M (a * b) (γb * γa) := by
    refine ⟨Subgroup.mul_mem _ hγb.1 hγa.1, ?_⟩
    rw [CuspForm.Gamma1Hecke.d_mul hγb.1 hγa.1, hγb.2, hγa.2, Nat.cast_mul, mul_comm]
  refine LinearMap.ext fun f => DFunLike.ext' ?_
  rw [Module.End.mul_apply, CuspForm.coe_diamondLinOne_apply hγa, CuspForm.coe_diamondLinOne_apply hγb,
    CuspForm.coe_diamondLinOne_apply hγ f, map_mul, SlashAction.slash_mul]

theorem diamondLinOne_pow {d : ℕ} (hd : Nat.Coprime d M) (m : ℕ) :
    CuspForm.diamondLinOne M k d ^ m = CuspForm.diamondLinOne M k (d ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, CuspForm.diamondLinOne_one]; rfl
  | succ m ih => rw [pow_succ, ih, diamondLinOne_mul (Nat.Coprime.pow_left m hd) hd, pow_succ]

theorem diamondLinOne_pow_totient {d : ℕ} (hd : Nat.Coprime d M) :
    CuspForm.diamondLinOne M k d ^ Nat.totient M = 1 := by
  rw [diamondLinOne_pow hd, diamondLinOne_congr (d' := 1)
    ((ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.pow_totient hd)), CuspForm.diamondLinOne_one]
  rfl

theorem hasNebentypus_of_diamond_eigen [NeZero M] (ε : DirichletCharacter ℂ M) (w : CuspForm (Gamma1 M) k)
    (hw : ∀ d : ℕ, Nat.Coprime d M → CuspForm.diamondLinOne M k d w = ε (d : ZMod M) • w) :
    CuspForm.HasNebentypus ε w := by
  intro γ hγ τ
  set δ : ZMod M := ((γ 1 1 : ℤ) : ZMod M) with hδ
  have hlift : CuspForm.IsDiamondLift M δ.val γ := ⟨hγ, by rw [ZMod.natCast_zmod_val]⟩
  have hcop : Nat.Coprime δ.val M := hlift.coprime
  have h1 := hw δ.val hcop
  rw [ZMod.natCast_zmod_val] at h1
  have h2 : (⇑(CuspForm.diamondLinOne M k δ.val w) : ℍ → ℂ) τ
      = ((⇑w : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) τ := by
    rw [CuspForm.coe_diamondLinOne_apply hlift]
  have e : Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) := rfl
  rw [h1, e, ← ModularForm.SL_slash, ModularForm.SL_slash_apply, ModularGroup.denom_apply] at h2
  rw [show (⇑(ε δ • w) : ℍ → ℂ) τ = ε δ * w τ from rfl] at h2

  set D : ℂ := ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero
      (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)) τ
    rwa [ModularGroup.denom_apply] at this
  have hDk : D ^ k ≠ 0 := zpow_ne_zero k hD0
  rw [zpow_neg, eq_mul_inv_iff_mul_eq₀ hDk] at h2
  rw [← h2]
  ring

end Diamond

section Span

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

variable {M : ℕ} {k : ℤ}

local notation "V" => CuspForm (Gamma1 M) k

attribute [local instance] ratModule

theorem mem_span_of_mem_VQ {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (hb : ∀ i, b i ∈ VQ M k)
    {f : V} (hf : f ∈ VQ M k) : f ∈ Submodule.span ℚ (Set.range b) := by
  by_contra hfn
  have hbQ : LinearIndependent ℚ (fun i => b i) :=
    b.linearIndependent.restrict_scalars (by
      intro x y hxy
      have : ((x : ℂ)) = (y : ℂ) := by simpa [Rat.smul_one_eq_cast] using hxy
      exact_mod_cast this)
  have h1 : LinearIndependent ℚ (Fin.cons f (fun i => b i) : Fin (n + 1) → V) :=
    linearIndependent_finCons.2 ⟨hbQ, hfn⟩
  have h2 : LinearIndependent ℂ (Fin.cons f (fun i => b i) : Fin (n + 1) → V) := by
    refine hli (n + 1) _ (fun i => ?_) h1
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hf
    · simpa using hb j
  have h3 := (linearIndependent_finCons.1 h2).2
  apply h3
  rw [show (Set.range fun i => b i) = Set.range b from rfl, b.span_eq]
  exact Submodule.mem_top

theorem finite_VQ {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (hb : ∀ i, b i ∈ VQ M k) :
    Module.Finite ℚ (VQ M k) := by
  have hle : (VQ M k) ≤ Submodule.span ℚ (Set.range b) := fun f hf => mem_span_of_mem_VQ b hb hf
  haveI : Module.Finite ℚ (Submodule.span ℚ (Set.range (fun i => b i))) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem span_VQ_eq_top {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (hb : ∀ i, b i ∈ VQ M k) :
    Submodule.span ℂ ((VQ M k : Submodule ℚ V) : Set V) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← b.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact hb i

end Span

section Semisimple

open CongruenceSubgroup ModularFormClass Polynomial
open scoped MatrixGroups

variable {M : ℕ} {k : ℤ}

local notation "V" => CuspForm (Gamma1 M) k

attribute [local instance] ratModule

theorem aeval_apply_of_eigen (T : Module.End ℂ V) {f : V} {μ : ℂ} (hf : T f = μ • f) (R : ℂ[X]) :
    Polynomial.aeval T R f = R.eval μ • f := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.eval_add, LinearMap.add_apply, hp, hq, add_smul]
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, mul_smul]
    congr 1
    induction m with
    | zero => rw [pow_zero, pow_zero, one_smul]; rfl
    | succ m ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, map_smul, hf, smul_smul, mul_comm]

theorem exists_separable_aeval_eq_zero_of_eigenbasis {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (T : Module.End ℂ V) (μ : Fin n → ℂ) (hTb : ∀ i, T (b i) = μ i • b i)
    (hT : ∀ f : V, f ∈ VQ M k → T f ∈ VQ M k) [Module.Finite ℚ (VQ M k)]
    (hspan : Submodule.span ℂ ((VQ M k : Submodule ℚ V) : Set V) = ⊤) :
    ∃ P : ℚ[X], P.Separable ∧ Polynomial.aeval T (P.map (algebraMap ℚ ℂ)) = 0 := by
  classical

  let A : Module.End ℚ (VQ M k) := (T.restrictScalars ℚ).restrict (fun f hf => hT f hf)
  have hA : ∀ w : VQ M k, ((A w : VQ M k) : V) = T (w : V) := fun w => rfl
  have hcoe : ∀ (r : ℚ[X]) (w : VQ M k),
      ((Polynomial.aeval A r w : VQ M k) : V) = Polynomial.aeval T (r.map (algebraMap ℚ ℂ)) (w : V) := by
    intro r w
    induction r using Polynomial.induction_on' generalizing w with
    | add p q hp hq =>
      rw [map_add, Polynomial.map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
        Submodule.coe_add, hp, hq]
    | monomial m a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, Submodule.coe_smul, algebraMap_smul]
      congr 1
      induction m generalizing w with
      | zero => rfl
      | succ m ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hA]

  have hlift : ∀ r : ℚ[X], Polynomial.aeval A r = 0 → Polynomial.aeval T (r.map (algebraMap ℚ ℂ)) = 0 := by
    intro r hr
    refine LinearMap.ext_on hspan (fun v hv => ?_)
    rw [LinearMap.zero_apply]
    have := hcoe r ⟨v, hv⟩
    rw [hr, LinearMap.zero_apply, ZeroMemClass.coe_zero] at this
    exact this.symm
  have hdown : ∀ r : ℚ[X], Polynomial.aeval T (r.map (algebraMap ℚ ℂ)) = 0 → Polynomial.aeval A r = 0 := by
    intro r hr
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [hcoe, hr]; rfl

  let P : ℚ[X] := minpoly ℚ A
  have hAint : IsIntegral ℚ A := IsIntegral.of_finite ℚ A
  have hP0 : P ≠ 0 := minpoly.ne_zero hAint
  refine ⟨P, ?_, hlift P (minpoly.aeval ℚ A)⟩

  rw [PerfectField.separable_iff_squarefree]
  intro q hq
  obtain ⟨r, hr⟩ := hq
  have hq0 : q ≠ 0 := fun h => hP0 (by rw [hr, h, zero_mul, zero_mul])
  have hr0 : r ≠ 0 := fun h => hP0 (by rw [hr, h, mul_zero])

  have heval : ∀ i, (P.map (algebraMap ℚ ℂ)).eval (μ i) = 0 := by
    intro i
    have h1 := aeval_apply_of_eigen T (hTb i) (P.map (algebraMap ℚ ℂ))
    rw [hlift P (minpoly.aeval ℚ A), LinearMap.zero_apply] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_right (b.ne_zero i)
  have hqr : Polynomial.aeval T ((q * r).map (algebraMap ℚ ℂ)) = 0 := by
    refine b.ext fun i => ?_
    rw [LinearMap.zero_apply, aeval_apply_of_eigen T (hTb i)]
    have h1 := heval i
    rw [hr, Polynomial.map_mul, Polynomial.map_mul, Polynomial.eval_mul, Polynomial.eval_mul] at h1
    rw [Polynomial.map_mul, Polynomial.eval_mul]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · rw [mul_eq_zero.1 h2 |>.elim id id, zero_mul, zero_smul]
    · rw [h2, mul_zero, zero_smul]
  have hdvd : P ∣ q * r := minpoly.dvd ℚ A (hdown _ hqr)
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd (mul_ne_zero hq0 hr0)
  rw [show P = q * q * r from hr, Polynomial.natDegree_mul (mul_ne_zero hq0 hq0) hr0,
    Polynomial.natDegree_mul hq0 hq0, Polynomial.natDegree_mul hq0 hr0] at hdeg
  have hq1 : q.natDegree = 0 := by omega
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0, hq1]
  rfl

end Semisimple

section Hecke

open CongruenceSubgroup ModularFormClass Polynomial
open scoped MatrixGroups ComplexConjugate

variable {M : ℕ}

local notation "V" => CuspForm (Gamma1 M) 2

attribute [local instance] ratModule

def GoodIdx (M : ℕ) (S : Finset ℕ) : Set (Nat.Primes ⊕ ℕ) :=
  {i | ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧ (i = Sum.inl ℓ ∨ i = Sum.inr (ℓ : ℕ))}

theorem image_X_goodIdx (M : ℕ) (S : Finset ℕ) :
    (MvPolynomial.X '' GoodIdx M S : Set HeckeAlgOne) =
      {x : HeckeAlgOne | ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
        (x = heckeGenOne ℓ ∨ x = diamondGen (ℓ : ℕ))} := by
  ext x
  constructor
  · rintro ⟨i, ⟨ℓ, h1, h2, h3⟩, rfl⟩
    rcases h3 with rfl | rfl
    · exact ⟨ℓ, h1, h2, Or.inl rfl⟩
    · exact ⟨ℓ, h1, h2, Or.inr rfl⟩
  · rintro ⟨ℓ, h1, h2, h3⟩
    rcases h3 with rfl | rfl
    · exact ⟨Sum.inl ℓ, ⟨ℓ, h1, h2, Or.inl rfl⟩, rfl⟩
    · exact ⟨Sum.inr (ℓ : ℕ), ⟨ℓ, h1, h2, Or.inr rfl⟩, rfl⟩

theorem mem_goodIdx_inl {S : Finset ℕ} {ℓ : Nat.Primes} :
    (Sum.inl ℓ : Nat.Primes ⊕ ℕ) ∈ GoodIdx M S ↔ ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S := by
  constructor
  · rintro ⟨ℓ', h1, h2, h3⟩
    rcases h3 with h | h
    · cases h; exact ⟨h1, h2⟩
    · cases h
  · rintro ⟨h1, h2⟩; exact ⟨ℓ, h1, h2, Or.inl rfl⟩

theorem mem_goodIdx_inr {S : Finset ℕ} {d : ℕ} :
    (Sum.inr d : Nat.Primes ⊕ ℕ) ∈ GoodIdx M S ↔ d.Prime ∧ ¬ d ∣ M ∧ d ∉ S := by
  constructor
  · rintro ⟨ℓ', h1, h2, h3⟩
    rcases h3 with h | h
    · cases h
    · cases h; exact ⟨ℓ'.prop, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩; exact ⟨⟨d, h0⟩, h1, h2, Or.inr rfl⟩

def lam (ε : DirichletCharacter ℂ M) (g : V) : Nat.Primes ⊕ ℕ → ℂ :=
  Sum.elim (fun ℓ => qCoeff (⇑g) ℓ) (fun d => ε (d : ZMod M))

def theta (ε : DirichletCharacter ℂ M) (g : V) : Nat.Primes ⊕ ℕ → ℂ :=
  Sum.elim (fun ℓ : Nat.Primes => qCoeff (⇑g) ℓ * (ε ((ℓ : ℕ) : ZMod M))⁻¹) (fun d : ℕ => (ε (d : ZMod M))⁻¹)

variable [NeZero M]

structure Realises (ρ : HeckeAlgOne →+* Module.End ℂ V) : Prop where
  hecke : ∀ (ℓ : Nat.Primes) (hℓM : ¬ (ℓ : ℕ) ∣ M), ρ (heckeGenOne ℓ) = CuspForm.heckeTLinOne 2 ℓ.prop hℓM
  dia : ∀ d : ℕ, Nat.Coprime d M → ρ (diamondGen d) = CuspForm.diamondLinOne M 2 d
  junk : ∀ d : ℕ, ¬ Nat.Coprime d M → ρ (diamondGen d) = 1
  hU : ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ∣ M → ∀ (f : V) (n : ℕ),
    qCoeff (⇑(ρ (heckeGenOne ℓ) f)) n = qCoeff (⇑f) (ℓ * n)

variable {ρ : HeckeAlgOne →+* Module.End ℂ (CuspForm (Gamma1 M) 2)}

theorem hrat_of_realises (hρ : Realises ρ)
    (hdiaRat : ∀ (d : ℕ) (f : V), f ∈ VQ M 2 → CuspForm.diamondLinOne M 2 d f ∈ VQ M 2)
    (i : Nat.Primes ⊕ ℕ) (f : V) (hf : f ∈ VQ M 2) : ρ (MvPolynomial.X i) f ∈ VQ M 2 := by
  rcases i with ℓ | d
  · rw [show (MvPolynomial.X (Sum.inl ℓ) : HeckeAlgOne) = heckeGenOne ℓ from rfl]
    by_cases hℓM : (ℓ : ℕ) ∣ M
    · intro n
      obtain ⟨a, ha⟩ := hf (ℓ * n)
      exact ⟨a, by rw [hρ.hU ℓ hℓM f n, ha]⟩
    · rw [hρ.hecke ℓ hℓM]
      have hd := hdiaRat ℓ f hf
      intro n
      obtain ⟨a, ha⟩ := hf (ℓ * n)
      obtain ⟨b, hb⟩ := hd (n / ℓ)
      refine ⟨a + (ℓ : ℚ) * (if (ℓ : ℕ) ∣ n then b else 0), ?_⟩
      rw [CuspForm.qCoeff_heckeTLinOne 2 ℓ.prop hℓM f n, ← ha, show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one]
      push_cast
      split_ifs with h
      · rw [hb]
      · simp
  · rw [show (MvPolynomial.X (Sum.inr d) : HeckeAlgOne) = diamondGen d from rfl]
    by_cases hd : Nat.Coprime d M
    · rw [hρ.dia d hd]; exact hdiaRat d f hf
    · rw [hρ.junk d hd]; exact hf

theorem hdiaRat_of_basis
    (hdia : ∀ d : ℕ, Nat.Coprime d M →
      ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ)
    {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (hb : ∀ (i : Fin n) (m : ℕ), qCoeff (⇑(b i)) m ∈ Set.range ((↑) : ℤ → ℂ))
    (d : ℕ) (f : V) (hf : f ∈ VQ M 2) : CuspForm.diamondLinOne M 2 d f ∈ VQ M 2 := by
  have hbQ : ∀ i, b i ∈ VQ M 2 := fun i => mem_VQ_of_int (hb i)
  have hmem := mem_span_of_mem_VQ b hbQ hf
  clear hf
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact mem_VQ_of_rat (fun m =>
      CuspForm.qCoeff_diamondLinOne_two_mem_range_ratCast_of_qCoeff_mem_range_intCast M hdia (b i) (hb i) d m)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx =>
    show CuspForm.diamondLinOne M 2 d ((q : ℂ) • x) ∈ VQ M 2
    rw [map_smul]
    exact Submodule.smul_mem (VQ M 2) q hx

theorem hss_of_realises (hρ : Realises ρ) (S : Finset ℕ)
    (hrat : ∀ (i : Nat.Primes ⊕ ℕ) (f : V), f ∈ VQ M 2 → ρ (MvPolynomial.X i) f ∈ VQ M 2)
    {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (hbQ : ∀ i, b i ∈ VQ M 2)
    {n' : ℕ} (b' : Module.Basis (Fin n') ℂ V)
    (hb' : ∀ i, ∃ ε' : DirichletCharacter ℂ M, CuspForm.HasNebentypus ε' (b' i) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ μ : ℂ, ∀ m : ℕ,
        qCoeff (⇑(b' i)) (p * m) + ε' (p : ZMod M) * (p : ℂ) ^ ((2 : ℤ) - 1) *
          (if p ∣ m then qCoeff (⇑(b' i)) (m / p) else 0) = μ * qCoeff (⇑(b' i)) m)
    (i : Nat.Primes ⊕ ℕ) (hi : i ∈ GoodIdx M S) :
    ∃ P : ℚ[X], P.Separable ∧ Polynomial.aeval (ρ (MvPolynomial.X i)) (P.map (algebraMap ℚ ℂ)) = 0 := by
  haveI := finite_VQ b hbQ
  rcases i with ℓ | d
  · obtain ⟨hℓM, -⟩ := mem_goodIdx_inl.1 hi

    have heig : ∀ j, ∃ μ : ℂ, ρ (MvPolynomial.X (Sum.inl ℓ)) (b' j) = μ • b' j := by
      intro j
      obtain ⟨ε', hε', hp⟩ := hb' j
      obtain ⟨μ, hμ⟩ := hp ℓ ℓ.prop hℓM
      refine ⟨μ, ?_⟩
      rw [show (MvPolynomial.X (Sum.inl ℓ) : HeckeAlgOne) = heckeGenOne ℓ from rfl, hρ.hecke ℓ hℓM]
      refine cusp_ext_of_qCoeff fun m => ?_
      rw [CuspForm.qCoeff_heckeTLinOne 2 ℓ.prop hℓM (b' j) m,
        hε'.diamondLinOne_apply_eq_smul ((Nat.Prime.coprime_iff_not_dvd ℓ.prop).2 hℓM), qCoeff_smul,
        qCoeff_smul, ← hμ m]
      split_ifs <;> ring
    choose μ hμ using heig
    exact exists_separable_aeval_eq_zero_of_eigenbasis b' _ μ hμ (fun f hf => hrat _ f hf)
      (span_VQ_eq_top b hbQ)
  · obtain ⟨hdp, hdM, -⟩ := mem_goodIdx_inr.1 hi
    have hd : Nat.Coprime d M := (Nat.Prime.coprime_iff_not_dvd hdp).2 hdM
    refine ⟨Polynomial.X ^ Nat.totient M - 1, ?_, ?_⟩
    · have := Polynomial.separable_X_pow_sub_C (1 : ℚ) (n := Nat.totient M)
        (by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos M)).ne') one_ne_zero
      simpa using this
    · rw [show (MvPolynomial.X (Sum.inr d) : HeckeAlgOne) = diamondGen d from rfl, hρ.dia d hd,
        Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, map_sub,
        map_pow, Polynomial.aeval_X, map_one, diamondLinOne_pow_totient hd, sub_self]

theorem heig_of_realises (hρ : Realises ρ) (S : Finset ℕ) {ε : DirichletCharacter ℂ M} {g : V}
    (hg : CuspForm.IsEigenformWith ε g) (i : Nat.Primes ⊕ ℕ) (hi : i ∈ GoodIdx M S) :
    ρ (MvPolynomial.X i) g = lam ε g i • g := by
  rcases i with ℓ | d
  · obtain ⟨hℓM, -⟩ := mem_goodIdx_inl.1 hi
    rw [show (MvPolynomial.X (Sum.inl ℓ) : HeckeAlgOne) = heckeGenOne ℓ from rfl, hρ.hecke ℓ hℓM]
    show CuspForm.heckeTLinOne 2 ℓ.prop hℓM g = qCoeff (⇑g) ℓ • g
    refine cusp_ext_of_qCoeff fun m => ?_
    rw [CuspForm.qCoeff_heckeTLinOne 2 ℓ.prop hℓM g m,
      hg.hasNebentypus.diamondLinOne_apply_eq_smul ((Nat.Prime.coprime_iff_not_dvd ℓ.prop).2 hℓM),
      qCoeff_smul, qCoeff_smul, ← hg.hecke_of_not_dvd ℓ.prop hℓM m]
    split_ifs <;> ring
  · obtain ⟨hdp, hdM, -⟩ := mem_goodIdx_inr.1 hi
    have hd : Nat.Coprime d M := (Nat.Prime.coprime_iff_not_dvd hdp).2 hdM
    rw [show (MvPolynomial.X (Sum.inr d) : HeckeAlgOne) = diamondGen d from rfl, hρ.dia d hd]
    exact hg.hasNebentypus.diamondLinOne_apply_eq_smul hd

theorem exists_prime_eq_mod (S : Finset ℕ) {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧ p ∉ S ∧ (p : ZMod M) = (d : ZMod M) := by
  have hu : IsUnit (d : ZMod M) := (ZMod.isUnit_iff_coprime d M).2 hd
  obtain ⟨p, hpgt, hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (M + S.sup id)
  refine ⟨p, hp, fun h => ?_, fun h => ?_, hpd⟩
  · have := Nat.le_of_dvd (NeZero.pos M) h
    omega
  · have : p ≤ S.sup id := Finset.le_sup (f := id) h
    omega

theorem hmult_of_realises (hρ : Realises ρ) (S : Finset ℕ) {ε : DirichletCharacter ℂ M} {g : V}
    (hg : CuspForm.IsPrimitiveForm ε g) (w : V)
    (hw : ∀ i ∈ GoodIdx M S, ρ (MvPolynomial.X i) w = lam ε g i • w) :
    ∃ c : ℂ, w = c • g := by

  have hdia : ∀ (p : ℕ), p.Prime → ¬ p ∣ M → p ∉ S → CuspForm.diamondLinOne M 2 p w = ε (p : ZMod M) • w := by
    intro p hp hpM hpS
    have := hw (Sum.inr p) (mem_goodIdx_inr.2 ⟨hp, hpM, hpS⟩)
    rwa [show (MvPolynomial.X (Sum.inr p) : HeckeAlgOne) = diamondGen p from rfl,
      hρ.dia p ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)] at this
  have hall : ∀ d : ℕ, Nat.Coprime d M → CuspForm.diamondLinOne M 2 d w = ε (d : ZMod M) • w := by
    intro d hd
    obtain ⟨p, hp, hpM, hpS, hpd⟩ := exists_prime_eq_mod S hd
    rw [← diamondLinOne_congr hpd, hdia p hp hpM hpS, hpd]
  have hneb : CuspForm.HasNebentypus ε w := hasNebentypus_of_diamond_eigen ε w hall

  have hT : ∀ (p : ℕ), p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
      qCoeff (⇑w) (p * n) + ε (p : ZMod M) * (p : ℂ) ^ ((2 : ℤ) - 1) *
        (if p ∣ n then qCoeff (⇑w) (n / p) else 0) = qCoeff (⇑g) p * qCoeff (⇑w) n := by
    intro p hp hpS hpM n
    have h1 := hw (Sum.inl ⟨p, hp⟩) (mem_goodIdx_inl.2 ⟨hpM, hpS⟩)
    rw [show (MvPolynomial.X (Sum.inl ⟨p, hp⟩) : HeckeAlgOne) = heckeGenOne ⟨p, hp⟩ from rfl,
      hρ.hecke ⟨p, hp⟩ hpM] at h1
    have h2 := congrArg (fun F : V => qCoeff (⇑F) n) h1
    simp only at h2
    rw [CuspForm.qCoeff_heckeTLinOne 2 hp hpM w n, qCoeff_smul,
      hneb.diamondLinOne_apply_eq_smul ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)] at h2

    rw [show lam ε g (Sum.inl ⟨p, hp⟩) = qCoeff (⇑g) p from rfl] at h2
    rw [← h2]
    show _ = qCoeff (⇑w) (p * n) + (p : ℂ) ^ ((2 : ℤ) - 1) *
      (if p ∣ n then qCoeff (⇑(ε (p : ZMod M) • w)) (n / p) else 0)
    split_ifs
    · rw [qCoeff_smul]; ring
    · simp
  exact ⟨qCoeff (⇑w) 1, CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M 2 ε g hg w hneb S hT⟩

theorem dirichlet_pow_totient (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    ε (ℓ : ZMod M) ^ Nat.totient M = 1 := by
  rw [← ZMod.coe_unitOfCoprime ℓ hℓ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
    Units.val_one, map_one]

theorem conj_dirichlet (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    conj (ε (ℓ : ZMod M)) = (ε (ℓ : ZMod M))⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (dirichlet_pow_totient ε hℓ)
    (Nat.totient_pos.2 (NeZero.pos M)).ne')).symm

theorem aeval_theta_eq_conj (S : Finset ℕ) {ε : DirichletCharacter ℂ M} {g : V}
    (hg : CuspForm.IsEigenformWith ε g) (s : HeckeAlgOne)
    (hs : s ∈ Algebra.adjoin ℤ (MvPolynomial.X '' GoodIdx M S : Set HeckeAlgOne)) :
    MvPolynomial.aeval (theta ε g) s = conj (MvPolynomial.aeval (lam ε g) s) := by
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rcases i with ℓ | d
    · obtain ⟨hℓM, -⟩ := mem_goodIdx_inl.1 hi
      show qCoeff (⇑g) ℓ * (ε ((ℓ : ℕ) : ZMod M))⁻¹ = conj (qCoeff (⇑g) ℓ)
      have hadj := CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M 2 ε g
        (ne_zero_of_qCoeff_one g hg.qCoeff_one) hg.hasNebentypus ℓ ℓ.prop hℓM (qCoeff (⇑g) ℓ)
        (fun n => hg.hecke_of_not_dvd ℓ.prop hℓM n)
      rw [hadj, MulChar.inv_apply_eq_inv', mul_comm]
    · obtain ⟨hdp, hdM, -⟩ := mem_goodIdx_inr.1 hi
      show (ε (d : ZMod M))⁻¹ = conj (ε (d : ZMod M))
      rw [conj_dirichlet ε ((Nat.Prime.coprime_iff_not_dvd hdp).2 hdM)]
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C, MvPolynomial.aeval_C, algebraMap_int_eq,
      eq_intCast, map_intCast]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, map_mul, hx, hy]

end Hecke

end C2aII
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne.C2aII"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
p2m_open "ModularCurve~IsCusp" in open  C2aII in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M) (S : Finset ℕ) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ t : ModularCurve.HeckeAlgOne,
      ∃ s ∈ (Algebra.adjoin ℤ
        {x : ModularCurve.HeckeAlgOne |
          ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
            (x = ModularCurve.heckeGenOne ℓ ∨ x = ModularCurve.diamondGen (ℓ : ℕ))}), ∃ u ∈ (Algebra.adjoin ℤ
        {x : ModularCurve.HeckeAlgOne |
          ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
            (x = ModularCurve.heckeGenOne ℓ ∨ x = ModularCurve.diamondGen (ℓ : ℕ))}),
        MvPolynomial.aeval
            (Sum.elim (fun ℓ : Nat.Primes => ModularFormClass.qCoeff g ℓ * (ε ((ℓ : ℕ) : ZMod M))⁻¹)
              (fun d : ℕ => (ε (d : ZMod M))⁻¹)) s ≠ 0 ∧
        ∀ x : ModularCurve.JOne M, (s * t) • x = u • x := by
  intro t
  letI := ModularCurve.heckeModuleOneBar M
  letI : Module ℚ (CuspForm (CongruenceSubgroup.Gamma1 M) 2) := ratModule M 2

  obtain ⟨Φ, hΦinj, hΦT, hΦD, hΦU⟩ := exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff M hin hcomm
  let ρ : HeckeAlgOne →+* Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2) :=
    Φ.comp (heckeEvalOneBarAux hcomm).toRingHom
  have hρ_apply : ∀ q, ρ q = Φ (heckeEvalOneBarAux hcomm q) := fun q => rfl
  have hgen : ∀ i : Nat.Primes ⊕ ℕ, ρ (MvPolynomial.X i)
      = Φ ⟨heckeDiamondGenBar M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ := by
    intro i; rw [hρ_apply, heckeEvalOneBarAux_X]
  have hinl : ∀ ℓ : Nat.Primes, ρ (heckeGenOne ℓ)
      = Φ ⟨heckeOperatorOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ := by
    intro ℓ
    rw [show heckeGenOne ℓ = (MvPolynomial.X (Sum.inl ℓ) : HeckeAlgOne) from rfl, hgen]
    have e0 : (⟨heckeDiamondGenBar M (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))))
        = ⟨heckeOperatorOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inl M ℓ)
    rw [e0]
  have hinr : ∀ d : ℕ, ρ (diamondGen d)
      = Φ ⟨diamondOneBar M d, Algebra.subset_adjoin (Set.mem_range_self (Sum.inr d))⟩ := by
    intro d
    rw [show diamondGen d = (MvPolynomial.X (Sum.inr d) : HeckeAlgOne) from rfl, hgen]
    have e0 : (⟨heckeDiamondGenBar M (Sum.inr d), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))))
        = ⟨diamondOneBar M d, Algebra.subset_adjoin (Set.mem_range_self (Sum.inr d))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inr M d)
    rw [e0]
  have hρ : Realises ρ := by
    refine ⟨fun ℓ hℓM => ?_, fun d hd => ?_, fun d hd => ?_, fun ℓ hℓM f n => ?_⟩
    · rw [hinl, hΦT ℓ hℓM]
    · rw [hinr, hΦD d hd]
    · rw [hinr]
      have h1 : diamondOneBar M d = 1 := by
        refine LinearMap.ext fun x => ?_
        rw [diamondOneBar_apply, diamondAutBar, diamondAut_of_not_coprime hd]
        have h0 : IsBaseChangeAutOf (AlgebraicClosure ℚ)
            (AlgEquiv.refl : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) AlgEquiv.refl := fun _ => rfl
        have h2 : baseChangeAut (AlgebraicClosure ℚ)
            (AlgEquiv.refl : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) = AlgEquiv.refl := by
          have hu := isBaseChangeAutOf_baseChangeAut ⟨_, h0⟩
          apply AlgEquiv.coe_algHom_injective
          refine IntermediateField.algHom_ext_of_eq_adjoin (F := AlgebraicClosure ℚ)
            (s := ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (x1FunctionField M : Set (LaurentSeries ℚ))) rfl ?_
          rintro _ ⟨y, hy, rfl⟩
          exact Subtype.ext ((hu ⟨y, hy⟩).trans (h0 ⟨y, hy⟩).symm)
        have h3 : AlgebraicCurve.SemilinearAut.ofAlgAut
            (AlgEquiv.refl : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M) = 1 :=
          map_one _
        rw [h2, h3, one_smul]
        rfl
      have h2 : (⟨diamondOneBar M d, Algebra.subset_adjoin (Set.mem_range_self (Sum.inr d))⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M)))) = 1 :=
        Subtype.ext h1
      rw [h2, map_one]
    · rw [hinl]
      exact hΦU ℓ hℓM f n

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast M
  have hbQ : ∀ i, b i ∈ VQ M 2 := fun i => mem_VQ_of_int (hb i)
  haveI := finite_VQ b hbQ
  obtain ⟨n', b', hb'⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen M 2
  have hdiaRat := hdiaRat_of_basis (fun d hd => (hin.2 d hd).1) b hb
  have hrat : ∀ (i : Nat.Primes ⊕ ℕ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2),
      f ∈ VQ M 2 → ρ (MvPolynomial.X i) f ∈ VQ M 2 := hrat_of_realises hρ hdiaRat

  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2) := Module.Finite.of_basis b
  obtain ⟨s, hs, u, hu, hne, hstu⟩ :=
    Module.End.exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne
      (VQ M 2) (hli) (span_VQ_eq_top b hbQ) ρ hrat (GoodIdx M S)
      (hss_of_realises hρ S hrat b hbQ b' hb') (lam ε g) g (ne_zero_of_qCoeff_one g hg.isEigenformWith.qCoeff_one)
      (heig_of_realises hρ S hg.isEigenformWith) (hmult_of_realises hρ S hg) t
  rw [image_X_goodIdx] at hs hu
  refine ⟨s, hs, u, hu, ?_, fun x => ?_⟩
  ·
    have h1 := aeval_theta_eq_conj S hg.isEigenformWith s (by rw [image_X_goodIdx]; exact hs)
    rw [show (Sum.elim (fun ℓ : Nat.Primes => ModularFormClass.qCoeff g ℓ * (ε ((ℓ : ℕ) : ZMod M))⁻¹)
        (fun d : ℕ => (ε (d : ZMod M))⁻¹)) = theta ε g from rfl, h1]
    exact (map_ne_zero_iff _ (RingHom.injective _)).2 hne
  ·
    have h1 : heckeEvalOneBarAux hcomm (s * t) = heckeEvalOneBarAux hcomm u := by
      apply hΦinj
      rw [← hρ_apply, ← hρ_apply, map_mul, hstu]
    rw [heckeModuleOneBar_smul_def hcomm, heckeModuleOneBar_smul_def hcomm, heckeEvalOneBar_apply,
      heckeEvalOneBar_apply, h1]

end
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne.C2aII"

end S_CuspForm_IsPrimitiveForm_exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_exists_mem_adjoin_good_aeval_ne_zero_mul_smul_eq_smul_jOne (solution)
