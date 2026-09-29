-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/289ba08b-ff72-54b1-abcf-c78246fe992c

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

noncomputable section

namespace SMOVpG1

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
    try simp only at h
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

p2m_open "ModularCurve~IsCusp CongruenceSubgroup ModularFormClass"
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

set_option maxHeartbeats 160000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open scoped IsMulCommutative in

theorem main
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (S : Finset ℕ) (Ω : Type) [Field Ω] [Algebra ℚ_[p] Ω]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* Ω)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (r : ℕ) (hr : r.Prime) (c d : R) (hd : IsIntegral ℤ d)
    (hcd : toC c = starRingEnd ℂ (ModularFormClass.qCoeff g r) * toC d)
    [Module HeckeAlgOne (JOne M)]
    (hsmul : ∀ (t : HeckeAlgOne) (x : JOne M), t • x = heckeEvalOneBar hcomm t x)
    (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* Ω)
    (hΛ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧
        Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * ψ (e ℓ) = 1) :
    Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨r, hr⟩) * ψ d = ψ c := by
  classical

  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[p] Ω).injective
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

  obtain ⟨G, -, hGq⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M 2 g
  have hG : CuspForm.IsPrimitiveForm ε⁻¹ G := CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M 2 ε g hg G hGq
  have hg0 : g ≠ 0 := ne_zero_of_qCoeff_one g hg.isEigenformWith.qCoeff_one

  obtain ⟨Φ, hΦinj, hΦT, hΦD, hΦU⟩ :=
    exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff M hin hcomm
  obtain ⟨rn, hrn⟩ : ∃ rn : MvPolynomial (Idx M) ℤ →+* HeckeAlgOne,
      ∀ i, rn (MvPolynomial.X i) = MvPolynomial.X (vIdx M i) :=
    ⟨MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlgOne) (fun i => MvPolynomial.X (vIdx M i)),
      fun i => MvPolynomial.eval₂_X _ _ _⟩
  obtain ⟨Φz, hΦzdef⟩ : ∃ Φz : MvPolynomial (Idx M) ℤ →+* Module.End ℂ (CuspForm (Gamma1 M) 2),
      ∀ P, Φz P = Φ (heckeEvalOneBarAux hcomm (rn P)) :=
    ⟨Φ.comp ((heckeEvalOneBarAux hcomm).toRingHom.comp rn), fun _ => rfl⟩
  have hΦzT : ∀ (ℓ : Nat.Primes) (hℓM : ¬ (ℓ : ℕ) ∣ M),
      Φz (MvPolynomial.X (Sum.inl ℓ)) = CuspForm.heckeTLinOne 2 ℓ.prop hℓM := by
    intro ℓ hℓM
    rw [hΦzdef, hrn]
    show Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inl ℓ))) = _
    rw [heckeEvalOneBarAux_X]
    have e0 : (⟨heckeDiamondGenBar M (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))))
        = ⟨heckeOperatorOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inl M ℓ)
    rw [e0, hΦT ℓ hℓM]
  have hΦzD : ∀ d : {d : ℕ // Nat.Coprime d M},
      Φz (MvPolynomial.X (Sum.inr d)) = CuspForm.diamondLinOne M 2 d := by
    intro d
    rw [hΦzdef, hrn]
    show Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inr (d : ℕ)))) = _
    rw [heckeEvalOneBarAux_X]
    have e0 : (⟨heckeDiamondGenBar M (Sum.inr (d : ℕ)), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))))
        = ⟨diamondOneBar M d, Algebra.subset_adjoin (Set.mem_range_self (Sum.inr (d : ℕ)))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inr M d)
    rw [e0, hΦD d.1 d.2]
  have hΦzU : ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ∣ M → ∀ (f : CuspForm (Gamma1 M) 2) (m : ℕ),
      qCoeff (⇑(Φz (MvPolynomial.X (Sum.inl ℓ)) f)) m = qCoeff (⇑f) (ℓ * m) := by
    intro ℓ hℓM f m
    rw [hΦzdef, hrn]
    show qCoeff (⇑(Φ (heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inl ℓ))) f)) m = _
    rw [heckeEvalOneBarAux_X]
    have e0 : (⟨heckeDiamondGenBar M (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
          ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))))
        = ⟨heckeOperatorOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ :=
      Subtype.ext (heckeDiamondGenBar_inl M ℓ)
    rw [e0]
    exact hΦU ℓ hℓM f m

  obtain ⟨ρ, hρ⟩ : ∃ ρ : HeckeAlgOne →+* ↥(rationalHeckeAlgebraOne p (JOne M)),
      ∀ t, (ρ t : Module.End ℚ_[p] (RationalTateModule p (JOne M))) = rationalHeckeRepOne p (JOne M) t :=
    ⟨(rationalHeckeRepOne p (JOne M)).codRestrict (rationalHeckeAlgebraOne p (JOne M))
      (rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p (JOne M)), fun _ => rfl⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ : MvPolynomial (Idx M) ℤ →+* Ω, ∀ P, μ P = Λ (ρ (rn P)) :=
    ⟨Λ.comp (ρ.comp rn), fun _ => rfl⟩
  have hμT : ∀ ℓ : Nat.Primes, μ (MvPolynomial.X (Sum.inl ℓ)) = Λ (rationalHeckeOne p (JOne M) ℓ) := by
    intro ℓ
    rw [hμdef, hrn]
    congr 1
    exact Subtype.ext (hρ _)
  have hμD : ∀ d : {d : ℕ // Nat.Coprime d M},
      μ (MvPolynomial.X (Sum.inr d)) = Λ (rationalDiamondOne p (JOne M) d) := by
    intro d
    rw [hμdef, hrn]
    congr 1
    exact Subtype.ext (hρ _)
  have hK0 : ∀ P : MvPolynomial (Idx M) ℤ, Φz P = 0 → μ P = 0 := by
    intro P hP
    rw [hΦzdef] at hP
    have h1 : heckeEvalOneBarAux hcomm (rn P) = 0 := hΦinj (by rw [map_zero]; exact hP)
    have h2 : heckeEvalOneBar hcomm (rn P) = 0 := by
      rw [heckeEvalOneBar_apply, h1]; rfl
    have h3 : rn P ∈ Module.annihilator HeckeAlgOne (JOne M) := by
      refine Module.mem_annihilator.2 fun x => ?_
      rw [hsmul, h2, LinearMap.zero_apply]
    have h4 : rationalHeckeRepOne p (JOne M) (rn P) = 0 := rationalHeckeRepOne_eq_zero_of_mem p _ h3
    have h5 : ρ (rn P) = 0 := Subtype.ext (by rw [hρ, h4]; rfl)
    rw [hμdef, h5, map_zero]

  obtain ⟨n, bs, hbs⟩ := CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast M 2
  haveI : FiniteDimensional ℂ (CuspForm (Gamma1 M) 2) := Module.Finite.of_basis bs
  have hbsQ : ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ∀ m : ℕ,
      qCoeff ((⇑(bs i) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) m ∈ Set.range (algebraMap ℚ ℂ) := by
    intro i γ hγ m
    obtain ⟨z, hz⟩ := hbs i γ hγ m
    exact ⟨z, by rw [← hz]; simp⟩
  have hbs1 : ∀ (i : Fin n) (m : ℕ), qCoeff (⇑(bs i)) m ∈ Set.range (algebraMap ℚ ℂ) := by
    intro i m
    have h := hbsQ i 1 (Subgroup.one_mem _) m
    rwa [SlashAction.slash_one] at h
  have hdiaQ : ∀ (i : Fin n) {dd : ℕ} (hdd : Nat.Coprime dd M) (m : ℕ),
      qCoeff (⇑(CuspForm.diamondLinOne M 2 dd (bs i))) m ∈ Set.range (algebraMap ℚ ℂ) := by
    intro i dd hdd m
    obtain ⟨γ, hγ⟩ := CuspForm.exists_isDiamondLift_of_coprime hdd
    rw [CuspForm.coe_diamondLinOne_apply hγ]
    exact hbsQ i γ hγ.1 m
  have hrat : ∀ i, RatOp bs (Φz (MvPolynomial.X i)) := by
    rintro (ℓ | ⟨dd, hdd⟩)
    · by_cases hℓM : (ℓ : ℕ) ∣ M
      · intro j k
        exact repr_rational_of_qCoeff_rational bs hbs1 _
          (fun m => by rw [hΦzU ℓ hℓM]; exact hbs1 j _) k
      · intro j k
        refine repr_rational_of_qCoeff_rational bs hbs1 _ (fun m => ?_) k
        obtain ⟨q1, h1⟩ := hbs1 j (ℓ * m)
        obtain ⟨q2, h2⟩ := hdiaQ j ((Nat.Prime.coprime_iff_not_dvd ℓ.prop).2 hℓM) (m / ℓ)
        refine ⟨q1 + (ℓ : ℚ) * (if (ℓ : ℕ) ∣ m then q2 else 0), ?_⟩
        have e2 : ((2 : ℤ) - 1) = 1 := by norm_num
        rw [hΦzT ℓ hℓM, CuspForm.qCoeff_heckeTLinOne, e2, zpow_one, ← h1]
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
      (Set.range fun ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S} => e ℓ.1) ∪ {c, d}
  have hbint : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsIntegral ℤ (b ℓ) := fun ℓ hℓ hℓM hℓS =>
    isIntegral_of_isIntegral_map toC htoC (by rw [hb ℓ hℓ hℓM hℓS]; exact isIntegral_qCoeff hg.isEigenformWith ℓ)
  have heint : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsIntegral ℤ (e ℓ) := fun ℓ hℓ hℓM hℓS =>
    isIntegral_of_isIntegral_map toC htoC (by
      rw [he ℓ hℓ hℓM hℓS]
      refine IsIntegral.of_pow (Nat.totient_pos.2 (NeZero.pos M)) ?_
      rw [dirichlet_pow_totient ε ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)]
      exact isIntegral_one)
  have hcint : IsIntegral ℤ c := isIntegral_of_isIntegral_map toC htoC (by
    rw [hcd]
    exact (isIntegral_conj (isIntegral_qCoeff hg.isEigenformWith r)).mul (hd.map toC.toIntAlgHom))
  have hG₀int : ∀ x ∈ G₀, IsIntegral ℤ x := by
    rintro x ((⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩ | ⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩) | hx)
    · exact hbint ℓ hℓ hℓM hℓS
    · exact heint ℓ hℓ hℓM hℓS
    · rcases hx with rfl | hx
      · exact hcint
      · rw [Set.mem_singleton_iff.1 hx]; exact hd
  let R₀ : Subalgebra ℤ R := Algebra.adjoin ℤ G₀
  have hR₀int : ∀ x ∈ R₀, IsIntegral ℤ x := fun x hx => by
    have hle : R₀ ≤ integralClosure ℤ R :=
      Algebra.adjoin_le fun y hy => (mem_integralClosure_iff ℤ R).2 (hG₀int y hy)
    exact (mem_integralClosure_iff ℤ R).1 (hle hx)
  have hbmem : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → b ℓ ∈ R₀ := fun ℓ hℓ hℓM hℓS =>
    Algebra.subset_adjoin (Or.inl (Or.inl ⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩))
  have hemem : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → e ℓ ∈ R₀ := fun ℓ hℓ hℓM hℓS =>
    Algebra.subset_adjoin (Or.inl (Or.inr ⟨⟨ℓ, hℓ, hℓM, hℓS⟩, rfl⟩))
  have hcmem : c ∈ R₀ := Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))
  have hdmem : d ∈ R₀ := Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton d)))
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
    IntermediateField.adjoin K₀ (Set.range fun i : Idx M => μ (MvPolynomial.X i))
  haveI : Algebra.IsAlgebraic K₀ F₁ := IntermediateField.isAlgebraic_adjoin fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact ((halg i).tower_top K₀).isIntegral
  let ιE : F₁ →ₐ[K₀] ℂ := IsAlgClosed.lift
  have hμmem : ∀ P : MvPolynomial (Idx M) ℤ, μ P ∈ F₁ := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => rw [eq_intCast MvPolynomial.C, map_intCast]; exact intCast_mem F₁ a
    | add f f' hf hf' => rw [map_add]; exact add_mem hf hf'
    | mul_X f i hf =>
      rw [map_mul]
      exact mul_mem hf (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
  obtain ⟨μc, hμc⟩ : ∃ μc : MvPolynomial (Idx M) ℤ →+* ℂ, ∀ P, μc P = ιE ⟨μ P, hμmem P⟩ :=
    ⟨(ιE : F₁ →+* ℂ).comp (μ.codRestrict F₁ hμmem), fun _ => rfl⟩
  have hK0c : ∀ P : MvPolynomial (Idx M) ℤ, Φz P = 0 → μc P = 0 := by
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
      μc (MvPolynomial.X (Sum.inl ⟨ℓ, hℓ⟩)) = qCoeff (⇑G) ℓ ∧
      μc (MvPolynomial.X (Sum.inr ⟨ℓ, (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM⟩)) = ε⁻¹ (ℓ : ZMod M) := by
    intro ℓ hℓ hℓM hℓS
    have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM
    obtain ⟨hΛT, hΛD⟩ := hΛ ℓ hℓ hℓM hℓS
    have hεℓ : ε (ℓ : ZMod M) ≠ 0 := dirichlet_ne_zero ε hcop

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
    have hadj := CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M 2 ε g hg0 hg.isEigenformWith.hasNebentypus
      ℓ hℓ hℓM (qCoeff (⇑g) ℓ) (fun m => hg.isEigenformWith.hecke_of_not_dvd hℓ hℓM m)
    refine ⟨?_, ?_⟩
    · rw [hGq, hadj, inv_apply_dirichlet, eq_inv_mul_iff_mul_eq₀ hεℓ, mul_comm]
      exact hTC
    · rw [inv_apply_dirichlet]
      exact eq_inv_of_mul_eq_one_left hDC

  let A₀ : Subalgebra ℂ (Module.End ℂ (CuspForm (Gamma1 M) 2)) :=
    Algebra.adjoin ℂ (Set.range fun i : Idx M => Φz (MvPolynomial.X i))
  haveI : IsMulCommutative A₀ := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    show Φz _ * Φz _ = Φz _ * Φz _
    rw [← map_mul, ← map_mul, mul_comm])
  obtain ⟨ΦC, hΦC⟩ : ∃ ΦC : MvPolynomial (Idx M) ℂ →ₐ[ℂ] Module.End ℂ (CuspForm (Gamma1 M) 2),
      ∀ i, ΦC (MvPolynomial.X i) = Φz (MvPolynomial.X i) := by
    refine ⟨A₀.val.comp (MvPolynomial.aeval fun i =>
      (⟨Φz (MvPolynomial.X i), Algebra.subset_adjoin (Set.mem_range_self i)⟩ : A₀)), fun i => ?_⟩
    show A₀.val (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    rfl
  have hKC := complexRelations bs Φz hrat ΦC hΦC μc hK0c
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector ΦC (fun i => μc (MvPolynomial.X i)) hKC

  have hOG : Φz (MvPolynomial.X (Sum.inl ⟨r, hr⟩)) G = qCoeff (⇑G) r • G := by
    by_cases hrM : r ∣ M
    · exact heckeU_eigen hG.isEigenformWith hr hrM _ (hΦzU ⟨r, hr⟩ hrM)
    · rw [hΦzT ⟨r, hr⟩ hrM]
      exact hecke_eigen hG.isEigenformWith hr hrM
  have hτ : μc (MvPolynomial.X (Sum.inl ⟨r, hr⟩)) = qCoeff (⇑G) r := by
    refine eigenvalue_eq_of_common_eigenvector hG S v hv0
      (fun ℓ => if h : ℓ.Prime then μc (MvPolynomial.X (Sum.inl ⟨ℓ, h⟩)) else 0)
      (fun dd => if h : Nat.Coprime dd M then μc (MvPolynomial.X (Sum.inr ⟨dd, h⟩)) else 0)
      (fun ℓ hℓ hℓM => ?_) (fun dd hdd => ?_) (fun ℓ hℓ hℓM hℓS => ?_) (fun ℓ hℓ hℓM hℓS => ?_)
      (Φz (MvPolynomial.X (Sum.inl ⟨r, hr⟩))) _ _ ?_ hOG
    · try dsimp only
      rw [dif_pos hℓ, ← hΦzT ⟨ℓ, hℓ⟩ hℓM, ← hΦC]
      exact hv _
    · try dsimp only
      rw [dif_pos hdd, ← hΦzD ⟨dd, hdd⟩, ← hΦC]
      exact hv _
    · try dsimp only
      rw [dif_pos hℓ]
      exact (hval ℓ hℓ hℓM hℓS).1
    · try dsimp only
      rw [dif_pos ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)]
      exact (hval ℓ hℓ hℓM hℓS).2
    · rw [← hΦC]
      exact hv _

  have key : (⟨μ (MvPolynomial.X (Sum.inl ⟨r, hr⟩)), hμmem _⟩ : F₁) * ⟨ψ d, hψmem ⟨d, hdmem⟩⟩
      = ⟨ψ c, hψmem ⟨c, hcmem⟩⟩ := by
    apply (ιE : F₁ →+* ℂ).injective
    rw [map_mul]
    show ιE ⟨μ (MvPolynomial.X (Sum.inl ⟨r, hr⟩)), hμmem _⟩ * ιE ⟨ψ d, hψmem ⟨d, hdmem⟩⟩
      = ιE ⟨ψ c, hψmem ⟨c, hcmem⟩⟩
    rw [← hμc, hιψ ⟨d, hdmem⟩, hιψ ⟨c, hcmem⟩, hτ, hGq]
    exact hcd.symm
  have key' := congrArg Subtype.val key
  rw [IntermediateField.coe_mul] at key'
  rw [← hμT ⟨r, hr⟩]
  exact key'

end Main

end SMOVpG1
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul.SMOVpG1"

end
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul.SMOVpG1"

p2m_open "ModularCurve~IsCusp" in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (S : Finset ℕ) (Ω : Type) [Field Ω] [Algebra ℚ_[p] Ω]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* Ω)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (r : ℕ) (hr : r.Prime) (c d : R) (hd : IsIntegral ℤ d)
    (hcd : toC c = starRingEnd ℂ (ModularFormClass.qCoeff g r) * toC d) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* Ω,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧
        Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * ψ (e ℓ) = 1) →
      Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨r, hr⟩) * ψ d = ψ c := by
  letI := ModularCurve.heckeModuleOneBar M
  intro Λ hΛ
  exact SMOVpG1.main hg p hin hcomm S Ω R toC htoC ψ b e hb he r hr c d hd hcd
    (fun t x => ModularCurve.heckeModuleOneBar_smul_def hcomm t x) Λ hΛ

end S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul (solution)
