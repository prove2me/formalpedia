-- Prove2me | solution 1 for CuspForm.exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3694d508-2238-550f-a089-814e9e167167

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure
import Theorems.Thm_CuspForm_twoCuspLattice_integralClosure_eq_span_twoCuspIntegralSet_bot
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice
import Theorems.Thm_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span
import Theorems.Thm_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum
import Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
import Theorems.Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"
p2m_attr_erase "simp" "CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace TTU

theorem S_mul_T_zpow_neg_mul_S_inv_eq_transpose (n : ℕ) :
    ModularGroup.S * ModularGroup.T ^ (-(n : ℤ)) * ModularGroup.S⁻¹ =
      Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ n) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_transpose, ← zpow_natCast, ModularGroup.coe_T_zpow,
    ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem alSlash_sum_slash_transpose_eq_heckeU_alSlash
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p) (k : ℤ)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ModularForm.alSlash W k
        (∑ j ∈ Finset.range q,
          f ∣[k] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) =
      ModularForm.heckeU k q (ModularForm.alSlash W k f) := by
  have hqQ : q ∣ M / p := by
    have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    rw [hM] at hqM
    exact ((Nat.Prime.dvd_mul hq).mp hqM).resolve_left
      (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp h))
  rw [ModularForm.heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div M p hpM hpM2 H hHp W q hq hqQ k f hf]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [S_mul_T_zpow_neg_mul_S_inv_eq_transpose]

theorem alGL_mul_alGL_eq {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) :
    W.alGL * W.alGL =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (q : ℝ) (by exact_mod_cast W.q_pos.ne')) *
        Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, ModularForm.AtkinLehnerDatum.sqUnitSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.mat,
      ModularForm.AtkinLehnerDatum.sqUnit, Matrix.GeneralLinearGroup.scalar, Matrix.map_apply,
      Matrix.natCast_apply] <;>
    ring

theorem slash_two_scalar (u : ℝˣ) (hu : 0 < (u : ℝ)) (φ : UpperHalfPlane → ℂ) :
    φ ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = φ := by
  funext τ
  rw [ModularForm.slash_apply, UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar]
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝ) = u * u := by
    rw [Matrix.GeneralLinearGroup.det_scalar]; simp [pow_two]
  have hpos : 0 < ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝ) := by
    rw [hdet]; exact mul_pos hu hu
  rw [UpperHalfPlane.σ, if_pos hpos, hdet]
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  simp only [abs_of_pos (mul_pos hu hu), Complex.ofReal_mul]
  norm_num
  field_simp

theorem alSlash_alSlash_two_eq_slash_sqUnit {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)
    (φ : UpperHalfPlane → ℂ) :
    ModularForm.alSlash W 2 (ModularForm.alSlash W 2 φ) =
      φ ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) := by
  rw [ModularForm.alSlash_def, ModularForm.alSlash_def, ← SlashAction.slash_mul, alGL_mul_alGL_eq,
    SlashAction.slash_mul, slash_two_scalar _ (by rw [Units.val_mk0]; exact_mod_cast W.q_pos)]

theorem exists_cuspForm_coe_eq_sum_slash_transpose
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (CohCarrier.GammaH M H) 2) :
    ∃ Y : CuspForm (CohCarrier.GammaH M H) 2,
      ⇑Y = ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ)) := by

  obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one W H hHp 2 f

  have hU := CuspForm.stableU M H (2 : ℤ) hq hqM
  have hUX : ⇑(CuspForm.heckeULinH 2 q X) = ModularForm.heckeU 2 q ⇑X := CuspForm.coe_heckeULinH_apply 2 hU X

  obtain ⟨Z, hZ⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one W H hHp 2
    (CuspForm.heckeULinH 2 q X)

  let u : CongruenceSubgroup.Gamma0 M := ⟨W.sqUnitSL, W.sqUnitSL_mem⟩
  let d : (ZMod M)ˣ := CohCarrier.gamma0Units M u⁻¹
  refine ⟨CuspForm.diamondLinH 2 d Z, ?_⟩
  have hD := CuspForm.stableD M H (2 : ℤ)
  rw [CuspForm.coe_diamondLinH_eq_slash 2 hD d (u⁻¹) rfl, hZ, hUX, hX,
    ← alSlash_sum_slash_transpose_eq_heckeU_alSlash M p hpM hpM2 H hHp W q hq hqM hqp 2 ⇑f
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ),
    alSlash_alSlash_two_eq_slash_sqUnit, ← SlashAction.slash_mul, ← map_mul]
  have hu : W.sqUnitSL * ((u⁻¹ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) = 1 := by
    show W.sqUnitSL * (W.sqUnitSL)⁻¹ = 1
    exact mul_inv_cancel _
  rw [hu, map_one, SlashAction.slash_one]

end TTU

namespace TTUForms

p2m_open "CuspForm ModularForm.CuspForm"

theorem twoCuspIntegralSet_mono {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} {p : ℕ}
    {A B : Subring ℂ} (hAB : A ≤ B) :
    twoCuspIntegralSet M H k p A ⊆ twoCuspIntegralSet M H k p B := by
  intro f hf t ht W n
  exact ⟨hAB (hf t ht W n).1, hAB (hf t ht W n).2⟩

theorem one_mem_strictPeriods (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := by
    have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
      rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hT0, ?_⟩
    have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
      ext; simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, ModularGroup.T]
    rw [this]; exact one_mem H
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem smul_slash_mapGL (k : ℤ) (γ : SL(2, ℤ)) (c : ℂ) (φ : UpperHalfPlane → ℂ) :
    (c • φ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      c • (φ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) :=
  ModularForm.SL_smul_slash k γ φ c

theorem units_eq_of_unitsMap_eq {M Q R : ℕ} [NeZero M] (hM : M = Q * R) (hQR : Nat.Coprime Q R)
    (hQ : Q ∣ M) (hR : R ∣ M) (u v : (ZMod M)ˣ)
    (h1 : ZMod.unitsMap hQ u = ZMod.unitsMap hQ v) (h2 : ZMod.unitsMap hR u = ZMod.unitsMap hR v) : u = v := by
  apply Units.ext
  have key : ∀ x : ZMod M, ZMod.castHom hQ (ZMod Q) x = 0 → ZMod.castHom hR (ZMod R) x = 0 → x = 0 := by
    intro x hxQ hxR
    rw [← ZMod.natCast_zmod_val x] at hxQ hxR ⊢
    rw [map_natCast, ZMod.natCast_eq_zero_iff] at hxQ hxR
    rw [ZMod.natCast_eq_zero_iff]
    have h := hQR.mul_dvd_of_dvd_of_dvd hxQ hxR
    rwa [← hM] at h
  have h1' := congrArg (fun w : (ZMod Q)ˣ => (w : ZMod Q)) h1
  have h2' := congrArg (fun w : (ZMod R)ˣ => (w : ZMod R)) h2
  simp only [ZMod.unitsMap_val] at h1' h2'
  rw [← sub_eq_zero]
  apply key
  · rw [map_sub, sub_eq_zero, ZMod.castHom_apply, ZMod.castHom_apply]; exact h1'
  · rw [map_sub, sub_eq_zero, ZMod.castHom_apply, ZMod.castHom_apply]; exact h2'

theorem map_heckeU {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (q : ℕ) (P : PowerSeries R) :
    PowerSeries.map φ (PowerSeries.heckeU q P) = PowerSeries.heckeU q (PowerSeries.map φ P) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_heckeU, PowerSeries.coeff_heckeU, PowerSeries.coeff_map]

theorem map_natCast_smul {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (D : ℕ) (P : PowerSeries R) :
    PowerSeries.map φ ((D : R) • P) = (D : S) • PowerSeries.map φ P := by
  ext n
  simp [PowerSeries.coeff_map]

section Frame

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (H : Subgroup (ZMod M)ˣ)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
  (Wd : ModularForm.AtkinLehnerDatum M (M / p))

set_option quotPrecheck false in
local notation "ZB" => (integralClosure ℤ ℂ).toSubring
set_option quotPrecheck false in
local notation "QQ" => (algebraMap ℚ ℂ).range

theorem coe_diamondLinH_one (x : CuspForm (CohCarrier.GammaH M H) 2) :
    ⇑(diamondLinH 2 (1 : (ZMod M)ˣ) x) = ⇑x := by
  rw [coe_diamondLinH_eq_slash 2 (CuspForm.stableD M H 2) 1 (1 : CongruenceSubgroup.Gamma0 M)
    (map_one (CohCarrier.gamma0Units M))]
  rw [show (((1 : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ))) = 1 from rfl, map_one, SlashAction.slash_one]

include hpM2 hHp in

theorem exists_not_dvd_and_mem_lattice_coe_eq_smul_alSlash
    (x : CuspForm (CohCarrier.GammaH M H) 2) (hx : x ∈ twoCuspLattice M H 2 p ZB) :
    ∃ D : ℕ, ¬ p ∣ D ∧ ∃ G : CuspForm (CohCarrier.GammaH M H) 2, G ∈ twoCuspLattice M H 2 p ZB ∧
      ⇑G = (D : ℂ) • ModularForm.alSlash Wd 2 ⇑x := by
  have hpp : p.Prime := Fact.out
  have hx' : x ∈ Submodule.span (↥ZB) (twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) := by
    have hset := CuspForm.twoCuspLattice_integralClosure_eq_span_twoCuspIntegralSet_bot p M hpM hpM2 H hHp
    rw [← SetLike.mem_coe, ← hset]
    exact hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨D, hD, g, hg1, hg2⟩ :=
        CuspForm.exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure
          p M H hpM hpM2 hHp Wd 1 y hy
      refine ⟨D, hD, g, twoCuspIntegralSet_subset_twoCuspLattice M H 2 p _ hg2, ?_⟩
      rw [hg1, coe_diamondLinH_one]
  | zero =>
      refine ⟨1, hpp.one_lt.ne' ∘ (Nat.dvd_one.mp ·) , 0, Submodule.zero_mem _, ?_⟩
      rw [CuspForm.coe_zero, ModularForm.alSlash_def, SlashAction.zero_slash, smul_zero]
  | add x y _ _ ihx ihy =>
      obtain ⟨Dx, hDx, Gx, hGxL, hGx⟩ := ihx
      obtain ⟨Dy, hDy, Gy, hGyL, hGy⟩ := ihy
      refine ⟨Dx * Dy, fun h => (hpp.dvd_mul.mp h).elim hDx hDy,
        ((Dy : ℂ) • Gx + (Dx : ℂ) • Gy), ?_, ?_⟩
      · refine Submodule.add_mem _ ?_ ?_
        · have : ((Dy : ℂ) • Gx) = (⟨(Dy : ℂ), natCast_mem _ Dy⟩ : ↥ZB) • Gx := by rw [Subring.smul_def]
          rw [this]; exact Submodule.smul_mem _ _ hGxL
        · have : ((Dx : ℂ) • Gy) = (⟨(Dx : ℂ), natCast_mem _ Dx⟩ : ↥ZB) • Gy := by rw [Subring.smul_def]
          rw [this]; exact Submodule.smul_mem _ _ hGyL
      · rw [CuspForm.coe_add, CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, hGx, hGy, CuspForm.coe_add,
          ModularForm.alSlash_add, smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (Dy : ℂ)]
  | smul a x _ ih =>
      obtain ⟨D, hD, G, hGL, hG⟩ := ih
      refine ⟨D, hD, a • G, Submodule.smul_mem _ _ hGL, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, hG,
        ModularForm.alSlash_smul, smul_comm]

end Frame

end TTUForms

namespace TTUForms

p2m_open "CuspForm ModularForm.CuspForm"

section Main

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (H : Subgroup (ZMod M)ˣ)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
  (Wd : ModularForm.AtkinLehnerDatum M (M / p))

set_option quotPrecheck false in
local notation "ZB" => (integralClosure ℤ ℂ).toSubring
set_option quotPrecheck false in
local notation "QQ" => (algebraMap ℚ ℂ).range

include hpM2 hHp in

theorem mem_twoCuspLattice_bot_of_mem_integralClosure_of_mem_range
    (G : CuspForm (CohCarrier.GammaH M H) 2)
    (hZ : G ∈ twoCuspLattice M H 2 p ZB) (hQ : G ∈ twoCuspLattice M H 2 p QQ) :
    G ∈ twoCuspLattice M H 2 p (⊥ : Subring ℂ) := by
  classical
  obtain ⟨n, b, hli, -, hlat⟩ := CuspForm.exists_linearIndependent_forall_twoCuspLattice_eq_span p M hpM hpM2 H hHp
  rw [hlat] at hZ hQ ⊢
  obtain ⟨cZ, hcZ⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hZ
  obtain ⟨cQ, hcQ⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hQ

  have hsumZ : ∑ i, ((cZ i : ℂ)) • b i = G := by
    rw [← hcZ]; exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
  have hsumQ : ∑ i, ((cQ i : ℂ)) • b i = G := by
    rw [← hcQ]; exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
  have hce : ∀ i, (cZ i : ℂ) = (cQ i : ℂ) := by
    have h0 : ∑ i, ((cZ i : ℂ) - (cQ i : ℂ)) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hsumZ, hsumQ, sub_self]
    intro i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)

  have hint : ∀ i, ∃ m : ℤ, (cQ i : ℂ) = m := by
    intro i
    obtain ⟨r, hr⟩ := (cQ i).2
    have h1 : IsIntegral ℤ (cZ i : ℂ) := (cZ i).2
    rw [hce i, ← hr] at h1
    have h2 : IsIntegral ℤ r := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp h1
    obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp h2
    refine ⟨m, ?_⟩
    rw [← hr, ← hm]
    simp
  choose m hm using hint
  refine (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨fun i => ⟨(m i : ℂ), intCast_mem _ (m i)⟩, ?_⟩
  rw [← hsumQ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subring.smul_def, hm i]

include hpM2 hHp hq hqM hqp Wd in

theorem exists_not_dvd_and_mem_and_coe_eq_smul
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (Y : CuspForm (CohCarrier.GammaH M H) 2)
    (hY : ⇑Y = ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) :
    ∃ D : ℕ, ¬ p ∣ D ∧ ∃ g : CuspForm (CohCarrier.GammaH M H) 2,
      g ∈ twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) ∧ g = (D : ℂ) • Y := by
  have hpp : p.Prime := Fact.out
  have hD2 := CuspForm.stableD M H (2 : ℤ)
  have hU := CuspForm.stableU M H (2 : ℤ) hq hqM

  have hfL : f ∈ twoCuspLattice M H 2 p ZB :=
    twoCuspIntegralSet_subset_twoCuspLattice M H 2 p _ (twoCuspIntegralSet_mono bot_le hf)
  obtain ⟨D₁, hD₁, G₁, hG₁L, hG₁⟩ :=
    exists_not_dvd_and_mem_lattice_coe_eq_smul_alSlash p M hpM hpM2 H hHp Wd f hfL

  have hUmem : (heckeULinH 2 q : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] _) ∈ heckeRingH M H 2 := by
    rw [← heckeGenH_U (∅ : Set ℕ) 2 q hq hqM]; exact heckeGenH_mem_heckeRingH _ _ _
  have hUG₁L : heckeULinH 2 q G₁ ∈ twoCuspLattice M H 2 p ZB := heckeRingH_apply_mem_twoCuspLattice hUmem hG₁L
  have hUG₁ : ⇑(heckeULinH 2 q G₁) = (D₁ : ℂ) • ModularForm.alSlash Wd 2 ⇑Y := by
    rw [coe_heckeULinH_apply 2 hU, hG₁, ModularForm.heckeU_smul, hY,
      TTU.alSlash_sum_slash_transpose_eq_heckeU_alSlash M p hpM hpM2 H hHp Wd q hq hqM hqp 2 ⇑f
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)]

  obtain ⟨D₂, hD₂, G₂, hG₂L, hG₂⟩ :=
    exists_not_dvd_and_mem_lattice_coe_eq_smul_alSlash p M hpM hpM2 H hHp Wd _ hUG₁L

  let u : CongruenceSubgroup.Gamma0 M := ⟨Wd.sqUnitSL, Wd.sqUnitSL_mem⟩
  have hdmem : (diamondLinH 2 (CohCarrier.gamma0Units M u⁻¹) : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] _) ∈
      heckeRingH M H 2 := by
    rw [← heckeGenH_dia (∅ : Set ℕ) 2]; exact heckeGenH_mem_heckeRingH _ _ _
  let G := diamondLinH 2 (CohCarrier.gamma0Units M u⁻¹) G₂
  have hGL : G ∈ twoCuspLattice M H 2 p ZB := heckeRingH_apply_mem_twoCuspLattice hdmem hG₂L
  have hG : ⇑G = ((D₁ * D₂ : ℕ) : ℂ) • ⇑Y := by
    show ⇑(diamondLinH 2 (CohCarrier.gamma0Units M u⁻¹) G₂) = _
    rw [coe_diamondLinH_eq_slash 2 hD2 _ (u⁻¹) rfl, hG₂, hUG₁, ModularForm.alSlash_smul,
      TTU.alSlash_alSlash_two_eq_slash_sqUnit, smul_smul, smul_slash_mapGL, ← SlashAction.slash_mul, ← map_mul]
    have hu : Wd.sqUnitSL * ((u⁻¹ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) = 1 := by
      show Wd.sqUnitSL * (Wd.sqUnitSL)⁻¹ = 1
      exact mul_inv_cancel _
    rw [hu, map_one, SlashAction.slash_one, Nat.cast_mul, mul_comm (D₂ : ℂ)]

  have hYQ := CuspForm.mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range
    p M hpM hpM2 H hHp q hq hqM hqp f (twoCuspIntegralSet_mono bot_le hf) Y hY
  have hGeq : G = ((D₁ * D₂ : ℕ) : ℂ) • Y := DFunLike.ext' (by rw [hG, CuspForm.IsGLPos.coe_smul])
  have hGQ : G ∈ twoCuspLattice M H 2 p QQ := by
    have : G = (⟨((D₁ * D₂ : ℕ) : ℂ), natCast_mem _ _⟩ : ↥QQ) • Y := by rw [Subring.smul_def]; exact hGeq
    rw [this]
    exact Submodule.smul_mem _ _ (twoCuspIntegralSet_subset_twoCuspLattice M H 2 p _ hYQ)

  have hGbot := mem_twoCuspLattice_bot_of_mem_integralClosure_of_mem_range p M hpM hpM2 H hHp G hGL hGQ
  exact ⟨D₁ * D₂, fun h => (hpp.dvd_mul.mp h).elim hD₁ hD₂, G,
    CuspForm.mem_twoCuspIntegralSet_of_mem_twoCuspLattice p M hpM H hHp G hGbot, hGeq⟩

end Main

end TTUForms

namespace TTUForms

p2m_open "CuspForm ModularForm.CuspForm"

section PinIdentity

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (H : Subgroup (ZMod M)ˣ)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
  (Wd : ModularForm.AtkinLehnerDatum M (M / p))

include hpM2 hHp hq hqM hqp in

theorem alSlash_diamondLinH_eq_heckeU_alSlash_diamondLinH
    (f Y : CuspForm (CohCarrier.GammaH M H) 2)
    (hY : ⇑Y = ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ)))
    (e : (ZMod M)ˣ) :
    ModularForm.alSlash Wd 2 ⇑(diamondLinH 2 e Y) =
      ModularForm.heckeU 2 q (ModularForm.alSlash Wd 2 ⇑(diamondLinH 2 e f)) := by
  have hU := CuspForm.stableU M H (2 : ℤ) hq hqM
  obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one Wd H hHp 2 f
  obtain ⟨Z₁, hZ₁⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one Wd H hHp 2 Y
  have hZ₁U : Z₁ = heckeULinH 2 q X := by
    apply DFunLike.ext'
    rw [hZ₁, hY, TTU.alSlash_sum_slash_transpose_eq_heckeU_alSlash M p hpM hpM2 H hHp Wd q hq hqM hqp 2 ⇑f
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ), ← hX, coe_heckeULinH_apply 2 hU]
  obtain ⟨e₁, h1a, h1b, h1c⟩ :=
    CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum Wd H 2 e f X hX
  obtain ⟨e₂, h2a, h2b, h2c⟩ :=
    CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum Wd H 2 e Y Z₁ hZ₁

  have hcop : Nat.Coprime (M / p) Wd.R :=
    Nat.isCoprime_iff_coprime.mp ⟨Wd.a, -Wd.b, by linear_combination Wd.bezout⟩
  have he12 : e₁ = e₂ := by
    refine units_eq_of_unitsMap_eq Wd.hM hcop (Dvd.intro Wd.R Wd.hM.symm) (Dvd.intro_left _ Wd.hM.symm) e₁ e₂ ?_ ?_
    · rw [map_mul] at h1b h2b
      rw [eq_inv_of_mul_eq_one_left h1b, eq_inv_of_mul_eq_one_left h2b]
    · rw [h1a, h2a]
  rw [h2c, hZ₁U, ← he12, ← (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H 2).2.2.2.1 q hq hqM e₁ X,
    coe_heckeULinH_apply 2 hU, h1c]

include hpM2 hHp hq hqM hqp in

theorem smul_heckeU_pin_eq_smul_pin
    (f Y : CuspForm (CohCarrier.GammaH M H) 2)
    (hY : ⇑Y = ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ)))
    (D : ℕ) (g : CuspForm (CohCarrier.GammaH M H) 2) (hg : g = (D : ℂ) • Y) (e : (ZMod M)ˣ)
    (D₀ : ℕ) (pfW₀ : PowerSeries ↥(integralClosure ℤ ℂ))
    (h₀ : pfW₀.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D₀ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)))
    (D₁ : ℕ) (pfW₁ : PowerSeries ↥(integralClosure ℤ ℂ))
    (h₁ : pfW₁.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D₁ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g))) :
    ((D * D₁ : ℕ) : ↥(integralClosure ℤ ℂ)) • PowerSeries.heckeU q pfW₀ =
      ((D₀ : ℕ) : ↥(integralClosure ℤ ℂ)) • pfW₁ := by
  have hU := CuspForm.stableU M H (2 : ℤ) hq hqM
  have hΓ := one_mem_strictPeriods M H

  obtain ⟨Xe, hXe⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one Wd H hHp 2
    (diamondLinH 2 e f)
  have hkey := alSlash_diamondLinH_eq_heckeU_alSlash_diamondLinH p M hpM hpM2 H hHp q hq hqM hqp Wd f Y hY e

  have hq0 : q ≠ 0 := hq.ne_zero
  have e0 : UpperHalfPlane.qExpansion 1 ((D₀ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) =
      (D₀ : ℂ) • UpperHalfPlane.qExpansion 1 ⇑Xe := by
    rw [← hXe, ModularForm.qExpansion_smul one_pos hΓ (D₀ : ℂ) Xe]
  have e1 : UpperHalfPlane.qExpansion 1 ((D₁ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g)) =
      ((D₁ * D : ℕ) : ℂ) • PowerSeries.heckeU q (UpperHalfPlane.qExpansion 1 ⇑Xe) := by
    rw [hg, LinearMap.map_smul, CuspForm.IsGLPos.coe_smul, ModularForm.alSlash_smul, hkey, ← hXe,
      ← coe_heckeULinH_apply 2 hU Xe, smul_smul, ← Nat.cast_mul,
      ModularForm.qExpansion_smul one_pos hΓ ((D₁ * D : ℕ) : ℂ) (heckeULinH 2 q Xe),
      coe_heckeULinH_apply 2 hU Xe, ModularFormClass.qExpansion_heckeU_eq_heckeU Xe hΓ hq0]

  apply PowerSeries.map_injective (algebraMap ↥(integralClosure ℤ ℂ) ℂ) Subtype.val_injective
  rw [map_natCast_smul, map_natCast_smul, map_heckeU, h₀, h₁, e0, e1, LinearMap.map_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  ring

end PinIdentity

end TTUForms

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) :
    ∃ (D : ℕ) (_ : ¬ p ∣ D) (g : CuspForm (CohCarrier.GammaH M H) 2)
      (_ : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
      (⇑g = (D : ℂ) • ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) ∧
      (∀ (D₀ : ℕ) (pfW₀ : PowerSeries ↥(integralClosure ℤ ℂ)),
        pfW₀.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
          UpperHalfPlane.qExpansion 1 ((D₀ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
        ∀ (D₁ : ℕ) (pfW₁ : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW₁.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D₁ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g)) →
          ((D * D₁ : ℕ) : ↥(integralClosure ℤ ℂ)) • PowerSeries.heckeU q pfW₀ =
            ((D₀ : ℕ) : ↥(integralClosure ℤ ℂ)) • pfW₁) := by
  obtain ⟨Y, hY⟩ := TTU.exists_cuspForm_coe_eq_sum_slash_transpose M p hpM hpM2 H hHp Wd q hq hqM hqp f
  obtain ⟨D, hD, g, hg, hgeq⟩ :=
    TTUForms.exists_not_dvd_and_mem_and_coe_eq_smul p M hpM hpM2 H hHp q hq hqM hqp Wd f hf Y hY
  refine ⟨D, hD, g, hg, ?_, ?_⟩
  · rw [hgeq, CuspForm.IsGLPos.coe_smul, hY]
  · intro D₀ pfW₀ h₀ D₁ pfW₁ h₁
    exact TTUForms.smul_heckeU_pin_eq_smul_pin p M hpM hpM2 H hHp q hq hqM hqp Wd f Y hY D g hgeq e
      D₀ pfW₀ h₀ D₁ pfW₁ h₁

end S_CuspForm_exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet
end P2MW
export P2MW.S_CuspForm_exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet (solution)
