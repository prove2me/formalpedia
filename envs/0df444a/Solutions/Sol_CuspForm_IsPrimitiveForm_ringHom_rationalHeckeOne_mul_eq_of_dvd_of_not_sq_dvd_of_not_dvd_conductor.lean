-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.ringHom_rationalHeckeOne_mul_eq_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/da5d5136-1a23-5668-9f1d-2678329c09e9

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule
import Theorems.Thm_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul
import Theorems.Thm_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
import Theorems.Thm_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero"
p2m_attr_erase "simp" "Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

namespace S9cf5

open scoped ComplexConjugate

theorem isIntegral_of_isIntegral_map {R : Type} [CommRing R] (toC : R →+* ℂ)
    (htoC : Function.Injective toC) {x : R} (hx : IsIntegral ℤ (toC x)) : IsIntegral ℤ x := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine ⟨P, hPm, htoC ?_⟩
  rw [Polynomial.eval₂_def] at hP
  rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_def]
  have e : toC.comp (algebraMap ℤ R) = algebraMap ℤ ℂ := RingHom.ext_int _ _
  rw [e]
  exact hP

theorem changeLevel_natCast {n m : ℕ} [NeZero m] (hm : n ∣ m) (χ : DirichletCharacter ℂ n)
    (a : ℕ) (ha : a.Coprime m) :
    DirichletCharacter.changeLevel hm χ (a : ZMod m) = χ (a : ZMod n) := by
  have hu : ((ZMod.unitOfCoprime a ha : (ZMod m)ˣ) : ZMod m) = (a : ZMod m) :=
    ZMod.coe_unitOfCoprime a ha
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast hm]

theorem isIntegral_apply_natCast {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (a : ℕ)
    (ha : a.Coprime m) : IsIntegral ℤ (χ (a : ZMod m)) := by
  have hu : ((ZMod.unitOfCoprime a ha : (ZMod m)ˣ) : ZMod m) = (a : ZMod m) :=
    ZMod.coe_unitOfCoprime a ha
  have hpow : χ (a : ZMod m) ^ Fintype.card (ZMod m)ˣ = 1 := by
    rw [← hu, ← MulChar.coe_toUnitHom, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one,
      map_one, Units.val_one]
  exact IsIntegral.of_pow Fintype.card_pos (by rw [hpow]; exact isIntegral_one)

end S9cf5

set_option maxHeartbeats 4000000 in
open scoped ComplexConjugate in
open ModularCurve S9cf5 in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (S : Finset ℕ) (Ω : Type) [Field Ω] [Algebra ℚ_[p] Ω]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* Ω)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M) (hqε : ¬ q ∣ ε.conductor)
    (hbq : toC (b q) = ModularFormClass.qCoeff g q) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* Ω,
      (∀ c : ℚ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) c)
          = algebraMap ℚ_[p] Ω c) →
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧
        Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * ψ (e ℓ) = 1) →
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → ℓ ≡ q [MOD M / q] →
        Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨q, hq⟩) * ψ (e ℓ) = ψ (b q) := by
  letI := ModularCurve.heckeModuleOneBar M
  intro Λ _hΛc hΛ ℓ hℓ hℓM hℓS hℓq
  have hgE : CuspForm.IsEigenformWith ε g := hg.isEigenformWith
  have hM0 : M ≠ 0 := NeZero.ne M
  have hMq : M / q ∣ M := Nat.div_dvd_of_dvd hqM
  have hMqne : M / q ≠ M := (Nat.div_lt_self (NeZero.pos M) hq.one_lt).ne

  obtain ⟨ε', hε, hdisj⟩ :=
    hgE.exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
      q hq hqM hq2 hqε

  have hsq : ModularFormClass.qCoeff g q ^ 2 = ε' (q : ZMod (M / q)) := by
    rcases hdisj with h | ⟨h', hh', hcoeff⟩
    · exact h
    · exfalso
      refine hg.not_eigenpacketOccursAt hMq hMqne ⟨ε', h', ?_, hh'.hasNebentypus, Nat.divisors M, ?_⟩
      · intro h0
        have h1 := hh'.qCoeff_one
        rw [h0, ModularFormClass.qCoeff, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero,
          map_zero] at h1
        exact zero_ne_one h1
      · intro p hp hpS
        have hpM : ¬ p ∣ M := fun hpM => hpS (Nat.mem_divisors.2 ⟨hpM, hM0⟩)
        have hpMq : ¬ p ∣ M / q := fun h => hpM (dvd_trans h hMq)
        refine ⟨?_, fun n => ?_⟩
        · show ε' (p : ZMod (M / q)) = ε (p : ZMod M)
          rw [hε, changeLevel_natCast _ ε' p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)]
        · have := hh'.hecke_of_not_dvd hp hpMq n
          rw [hcoeff p hp hpM] at this
          exact this

  have hg' : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε') g := by
    rw [← hε]; exact hg
  have hnorm : ‖ModularFormClass.qCoeff g q‖ ^ 2 = (q : ℝ) ^ ((2 : ℤ) - 2) :=
    CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd M 2 hq hqM hq2 ε' g hg'
  have hnorm1 : ‖ModularFormClass.qCoeff g q‖ ^ 2 = (1 : ℝ) := by
    rw [hnorm]; norm_num

  have hcc : conj (ModularFormClass.qCoeff g q) * ModularFormClass.qCoeff g q = 1 := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, hnorm1, Complex.ofReal_one]
  have hkey : conj (ModularFormClass.qCoeff g q) * ε' (q : ZMod (M / q)) =
      ModularFormClass.qCoeff g q := by
    rw [← hsq, pow_two, ← mul_assoc, hcc, one_mul]

  have hℓcop : ℓ.Coprime M := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM
  have heℓ : toC (e ℓ) = ε' (q : ZMod (M / q)) := by
    rw [he ℓ hℓ hℓM hℓS, hε, changeLevel_natCast _ ε' ℓ hℓcop,
      (ZMod.natCast_eq_natCast_iff ℓ q (M / q)).mpr hℓq]

  have hint : IsIntegral ℤ (e ℓ) := by
    refine isIntegral_of_isIntegral_map toC htoC ?_
    rw [he ℓ hℓ hℓM hℓS]
    exact isIntegral_apply_natCast ε ℓ hℓcop

  have hcd : toC (b q) = conj (ModularFormClass.qCoeff g q) * toC (e ℓ) := by
    rw [hbq, heℓ, hkey]
  exact hg.ringHom_rationalHeckeOne_mul_eq_of_eq_conj_qCoeff_mul p hin hcomm S Ω R toC htoC ψ
    b e hb he q hq (b q) (e ℓ) hint hcd Λ hΛ

end S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_ringHom_rationalHeckeOne_mul_eq_of_dvd_of_not_sq_dvd_of_not_dvd_conductor (solution)
