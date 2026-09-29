-- Prove2me | solution 1 for CohCarrier.finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ad950a63-74aa-5bb2-b31e-d536ce162431

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_Newforms
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_gammaH
import Mathlib
import Theorems.Thm_Module_End_finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update
import Theorems.Thm_Matrix_charpoly_of_uString
import Theorems.Thm_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero"
p2m_attr_erase "simp" "CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

open Polynomial

namespace CESCount

open Finset

section BoxOn

variable {D : ℕ} {P : Finset ℕ}

theorem ne_zero_of_mem_divisorsOn {d : ℕ} (h : d ∈ Nat.divisors D) : d ≠ 0 :=
  (Nat.pos_of_mem_divisors h).ne'

theorem ne_zero_of_mem_divisorsOn' {d : ℕ} (h : d ∈ Nat.divisors D) : D ≠ 0 :=
  (Nat.mem_divisors.mp h).2

def boxCoordOn (P : Finset ℕ) (d : ↥(Nat.divisors D)) (q : ↥P) : Fin (D.factorization q + 1) :=
  ⟨(d : ℕ).factorization q, Nat.lt_succ_of_le
    ((Nat.factorization_le_iff_dvd (ne_zero_of_mem_divisorsOn d.2) (ne_zero_of_mem_divisorsOn' d.2)).mpr
      (Nat.dvd_of_mem_divisors d.2) q)⟩

@[scoped simp] theorem boxCoordOn_val (d : ↥(Nat.divisors D)) (q : ↥P) :
    ((boxCoordOn P d q : Fin (D.factorization q + 1)) : ℕ) = (d : ℕ).factorization q := rfl

def ofBoxOn (f : (q : ↥P) → Fin (D.factorization q + 1)) : ℕ :=
  ∏ q ∈ P.attach, (q : ℕ) ^ (f q : ℕ)

theorem ofBoxOn_ne_zero (hP : ∀ q ∈ P, q.Prime) (f : (q : ↥P) → Fin (D.factorization q + 1)) : ofBoxOn f ≠ 0 := by
  rw [ofBoxOn, Finset.prod_ne_zero_iff]
  intro q _
  exact pow_ne_zero _ (hP q q.2).ne_zero

theorem factorization_ofBoxOn (hP : ∀ q ∈ P, q.Prime) (f : (q : ↥P) → Fin (D.factorization q + 1)) (p : ℕ) :
    (ofBoxOn f).factorization p = if hp : p ∈ P then ((f ⟨p, hp⟩ : Fin _) : ℕ) else 0 := by
  have hpow : ∀ q : ↥P, ((q : ℕ) ^ (f q : ℕ)).factorization = Finsupp.single (q : ℕ) (f q : ℕ) :=
    fun q => (hP q q.2).factorization_pow
  rw [ofBoxOn, Nat.factorization_prod (fun (q : ↥P) _ => pow_ne_zero _ (hP q q.2).ne_zero),
    Finsupp.finsetSum_apply]
  simp_rw [hpow, Finsupp.single_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single (⟨p, hp⟩ : ↥P)]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro h
      exact hq (Subtype.ext h)
    · intro h
      exact absurd (Finset.mem_attach _ _) h
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro h
    exact hp (h ▸ q.2)

theorem ofBoxOn_dvd (hP : ∀ q ∈ P, q.Prime) (hD : D ≠ 0) (f : (q : ↥P) → Fin (D.factorization q + 1)) : ofBoxOn f ∣ D := by
  rw [← Nat.factorization_le_iff_dvd (ofBoxOn_ne_zero hP f) hD]
  intro p
  rw [factorization_ofBoxOn hP]
  split_ifs with hp
  · exact Nat.le_of_lt_succ (f ⟨p, hp⟩).2
  · exact Nat.zero_le _

theorem factorization_eq_zero_of_not_mem (hDP : D.primeFactors ⊆ P) (d : ↥(Nat.divisors D)) {p : ℕ}
    (hp : p ∉ P) : (d : ℕ).factorization p = 0 := by
  by_cases hpp : p.Prime
  · apply Nat.factorization_eq_zero_of_not_dvd
    intro hpd
    exact hp (hDP (Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Nat.dvd_of_mem_divisors d.2),
      ne_zero_of_mem_divisorsOn' d.2⟩))
  · exact Nat.factorization_eq_zero_of_not_prime _ hpp

theorem ofBoxOn_boxCoordOn (hP : ∀ q ∈ P, q.Prime) (hDP : D.primeFactors ⊆ P) (d : ↥(Nat.divisors D)) :
    ofBoxOn (boxCoordOn P d) = (d : ℕ) := by
  apply Nat.eq_of_factorization_eq (ofBoxOn_ne_zero hP _) (ne_zero_of_mem_divisorsOn d.2)
  intro p
  rw [factorization_ofBoxOn hP]
  split_ifs with hp
  · rfl
  · exact (factorization_eq_zero_of_not_mem hDP d hp).symm

variable (D P) in

def boxEquivOn (hP : ∀ q ∈ P, q.Prime) (hDP : D.primeFactors ⊆ P) (hD : D ≠ 0) :
    ↥(Nat.divisors D) ≃ ((q : ↥P) → Fin (D.factorization q + 1)) where
  toFun := boxCoordOn P
  invFun f := ⟨ofBoxOn f, Nat.mem_divisors.mpr ⟨ofBoxOn_dvd hP hD f, hD⟩⟩
  left_inv d := Subtype.ext (ofBoxOn_boxCoordOn hP hDP d)
  right_inv f := by
    funext q
    apply Fin.ext
    show (ofBoxOn f).factorization q = _
    rw [factorization_ofBoxOn hP, dif_pos q.2]

theorem boxEquivOn_apply_val (hP : ∀ q ∈ P, q.Prime) (hDP : D.primeFactors ⊆ P) (hD : D ≠ 0)
    (d : ↥(Nat.divisors D)) (q : ↥P) :
    ((boxEquivOn D P hP hDP hD d q : Fin _) : ℕ) = (d : ℕ).factorization q := rfl

theorem dvd_iff_factorization_pos (hP : ∀ q ∈ P, q.Prime) (d : ↥(Nat.divisors D)) (q : ↥P) :
    (q : ℕ) ∣ (d : ℕ) ↔ 0 < (d : ℕ).factorization q :=
  (hP q q.2).dvd_iff_one_le_factorization (ne_zero_of_mem_divisorsOn d.2)

theorem mul_dvd_iff_factorization_succ_le (hP : ∀ q ∈ P, q.Prime) (d : ↥(Nat.divisors D)) (q : ↥P) :
    (d : ℕ) * q ∣ D ↔ (d : ℕ).factorization q + 1 ≤ D.factorization q := by
  have hd0 := ne_zero_of_mem_divisorsOn d.2
  have hD := ne_zero_of_mem_divisorsOn' d.2
  have hq := hP q q.2
  have hfac : ((d : ℕ) * q).factorization = (d : ℕ).factorization + Finsupp.single (q : ℕ) 1 := by
    rw [Nat.factorization_mul hd0 hq.ne_zero, hq.factorization]
  constructor
  · intro h
    have := (Nat.factorization_le_iff_dvd (mul_ne_zero hd0 hq.ne_zero) hD).mpr h q
    rwa [hfac, Finsupp.add_apply, Finsupp.single_eq_same] at this
  · intro h
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hd0 hq.ne_zero) hD, hfac]
    intro p
    rw [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with hpq
    · subst hpq
      exact h
    · rw [Nat.add_zero]
      exact (Nat.factorization_le_iff_dvd hd0 hD).mpr (Nat.dvd_of_mem_divisors d.2) p

theorem div_mem_divisorsOn {d : ℕ} (hd : d ∈ Nat.divisors D) (q : ℕ) (hq : q ∣ d) :
    d / q ∈ Nat.divisors D :=
  Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hq).trans (Nat.dvd_of_mem_divisors hd),
    ne_zero_of_mem_divisorsOn' hd⟩

theorem boxEquivOn_div (hP : ∀ q ∈ P, q.Prime) (hDP : D.primeFactors ⊆ P) (hD : D ≠ 0) (d : ↥(Nat.divisors D)) (q : ↥P)
    (hq : (q : ℕ) ∣ (d : ℕ)) (q' : ↥P) :
    ((boxEquivOn D P hP hDP hD ⟨(d : ℕ) / q, div_mem_divisorsOn d.2 q hq⟩ q' : Fin _) : ℕ) =
      ((Function.update (boxEquivOn D P hP hDP hD d) q
        ⟨(d : ℕ).factorization q - 1,
          lt_of_le_of_lt (Nat.sub_le _ _) (boxEquivOn D P hP hDP hD d q).2⟩ q' : Fin _) : ℕ) := by
  rw [boxEquivOn_apply_val]
  show ((d : ℕ) / q).factorization q' = _
  rw [Nat.factorization_div hq, (hP q q.2).factorization]
  by_cases h : q' = q
  · subst h
    simp [Function.update_self]
  · rw [Function.update_of_ne h, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg,
      Nat.sub_zero, boxEquivOn_apply_val]
    intro h'
    exact h (Subtype.ext h'.symm)

theorem boxEquivOn_mul (hP : ∀ q ∈ P, q.Prime) (hDP : D.primeFactors ⊆ P) (hD : D ≠ 0) (d : ↥(Nat.divisors D)) (q : ↥P)
    (h : (d : ℕ) * q ∣ D) (q' : ↥P) :
    ((boxEquivOn D P hP hDP hD ⟨(d : ℕ) * q, Nat.mem_divisors.mpr ⟨h, hD⟩⟩ q' : Fin _) : ℕ) =
      ((Function.update (boxEquivOn D P hP hDP hD d) q
        ⟨(d : ℕ).factorization q + 1,
          Nat.lt_succ_of_le ((mul_dvd_iff_factorization_succ_le hP d q).mp h)⟩ q' : Fin _) : ℕ) := by
  rw [boxEquivOn_apply_val]
  show ((d : ℕ) * q).factorization q' = _
  rw [show ((d : ℕ) * q).factorization q' = (d : ℕ).factorization q' + (Finsupp.single (q : ℕ) 1) q' from by
    rw [Nat.factorization_mul (ne_zero_of_mem_divisorsOn d.2) (hP q q.2).ne_zero, (hP q q.2).factorization]
    rfl]
  by_cases hq' : q' = q
  · subst hq'
    simp [Function.update_self]
  · rw [Function.update_of_ne hq', Finsupp.single_apply, if_neg, Nat.add_zero, boxEquivOn_apply_val]
    intro h'
    exact hq' (Subtype.ext h'.symm)

end BoxOn

namespace StringCountAux

variable {F : Type} [Field F]

theorem comap_maxGenEigenspace_eq_of_comm
    {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (j : X →ₗ[F] Y) (hj : Function.Injective j) (f' : Module.End F X) (f : Module.End F Y)
    (h : j ∘ₗ f' = f ∘ₗ j) (μ : F) :
    (f.maxGenEigenspace μ).comap j = f'.maxGenEigenspace μ := by
  have hc : ∀ y, f (j y) = j (f' y) := fun y => (LinearMap.congr_fun h y).symm
  have hk : ∀ (k : ℕ) (x : X), ((f - μ • (1 : Module.End F Y)) ^ k) (j x) =
      j (((f' - μ • (1 : Module.End F X)) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [LinearMap.sub_apply, hc]
  ext x
  simp only [Submodule.mem_comap, Module.End.mem_maxGenEigenspace, hk, map_eq_zero_iff j hj]

theorem finrank_iInf_maxGenEigenspace_eq_of_equiv
    {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
    {Q : Type} (Ψ : V' ≃ₗ[F] V) (U : Q → Module.End F V) (U' : Q → Module.End F V')
    (h : ∀ q, Ψ.toLinearMap ∘ₗ U' q = U q ∘ₗ Ψ.toLinearMap) (lam : Q → F) :
    Module.finrank F ↥(⨅ q, Module.End.maxGenEigenspace (U q) (lam q)) =
      Module.finrank F ↥(⨅ q, Module.End.maxGenEigenspace (U' q) (lam q)) := by
  have hc : (⨅ q, Module.End.maxGenEigenspace (U q) (lam q)).comap Ψ.toLinearMap =
      ⨅ q, Module.End.maxGenEigenspace (U' q) (lam q) := by
    rw [Submodule.comap_iInf]
    exact iInf_congr fun q => comap_maxGenEigenspace_eq_of_comm _ Ψ.injective _ _ (h q) (lam q)
  rw [← hc, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

variable {Q : Type} [Fintype Q] [DecidableEq Q] (ι : Q → Type) [∀ q, Fintype (ι q)] [∀ q, DecidableEq (ι q)]

noncomputable def coordOp (q : Q) (C : Matrix (ι q) (ι q) F) : Module.End F (((q : Q) → ι q) → F) where
  toFun v := fun j => ∑ i : ι q, C (j q) i * v (Function.update j q i)
  map_add' v w := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype Q] [∀ q, DecidableEq (ι q)] in
theorem coordOp_apply (q : Q) (C : Matrix (ι q) (ι q) F) (v : ((q : Q) → ι q) → F) (j : (q : Q) → ι q) :
    coordOp ι q C v j = ∑ i : ι q, C (j q) i * v (Function.update j q i) := rfl

theorem coordOp_single (q : Q) (C : Matrix (ι q) (ι q) F) (j' : (q : Q) → ι q) :
    coordOp ι q C (Pi.single j' 1) =
      ∑ i : ι q, C i (j' q) • (Pi.single (Function.update j' q i) (1 : F) : ((q : Q) → ι q) → F) := by
  funext j
  rw [coordOp_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

  rw [Finset.sum_eq_single (j' q), Finset.sum_eq_single (j q)]
  · by_cases hj : j = Function.update j' q (j q)
    · rw [if_pos hj, if_pos]
      rw [hj, Function.update_idem, Function.update_eq_self]
    · rw [if_neg hj, if_neg]
      intro h
      apply hj
      rw [← h, Function.update_idem, Function.update_eq_self]
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (by rw [h, Function.update_self])
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (by rw [← h, Function.update_self])
  · intro h
    exact absurd (Finset.mem_univ _) h

end StringCountAux

end CESCount
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

namespace CESCount

section Strings

variable {F : Type} [Field F]

def strMat (e : ℕ) (a b : F) : Matrix (Fin (e + 1)) (Fin (e + 1)) F :=
  Matrix.of fun i j : Fin (e + 1) =>
    if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
    else (if (i : ℕ) + 1 = (j : ℕ) then (1 : F) else 0)

theorem strMat_apply (e : ℕ) (a b : F) (i j : Fin (e + 1)) :
    strMat e a b i j = if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
      else (if (i : ℕ) + 1 = (j : ℕ) then (1 : F) else 0) := rfl

theorem charpoly_strMat (e : ℕ) (a b : F) :
    (strMat e a b).charpoly = if e = 0 then X - C a else X ^ (e - 1) * (X ^ 2 - C a * X + C b) :=
  Matrix.charpoly_of_uString F e a b

variable {M : Type} [AddCommGroup M] [Module F M]

theorem sum_strMat_smul_of_ne_zero (e : ℕ) (a b : F) (w : Fin (e + 1) → M) (j₀ : Fin (e + 1))
    (hj : (j₀ : ℕ) ≠ 0) :
    ∑ i, strMat e a b i j₀ • w i = w ⟨(j₀ : ℕ) - 1, by omega⟩ := by
  rw [Finset.sum_eq_single (⟨(j₀ : ℕ) - 1, by omega⟩ : Fin (e + 1))]
  · rw [strMat_apply, if_neg hj, if_pos, one_smul]
    show (j₀ : ℕ) - 1 + 1 = (j₀ : ℕ)
    omega
  · intro i _ hi
    rw [strMat_apply, if_neg hj, if_neg, zero_smul]
    intro h
    apply hi
    apply Fin.ext
    show (i : ℕ) = (j₀ : ℕ) - 1
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_strMat_smul_of_eq_zero_of_pos (e : ℕ) (he : 0 < e) (a b : F) (w : Fin (e + 1) → M)
    (j₀ : Fin (e + 1)) (hj : (j₀ : ℕ) = 0) :
    ∑ i, strMat e a b i j₀ • w i = a • w j₀ - b • w ⟨1, by omega⟩ := by
  rw [Fintype.sum_eq_add j₀ (⟨1, by omega⟩ : Fin (e + 1))]
  · rw [strMat_apply, if_pos hj, if_pos hj, strMat_apply, if_pos hj, if_neg, if_pos rfl, neg_smul,
      sub_eq_add_neg]
    show ¬ ((1 : ℕ) = 0)
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [hj] at this
    omega
  · rintro i ⟨hi0, hi1⟩
    rw [strMat_apply, if_pos hj, if_neg, if_neg, zero_smul]
    · intro h
      exact hi1 (Fin.ext h)
    · intro h
      exact hi0 (Fin.ext (h.trans hj.symm))

theorem sum_strMat_smul_of_eq_zero_of_eq_zero (e : ℕ) (he : e = 0) (a b : F) (w : Fin (e + 1) → M)
    (j₀ : Fin (e + 1)) :
    ∑ i, strMat e a b i j₀ • w i = a • w j₀ := by
  have hval : ∀ i : Fin (e + 1), (i : ℕ) = 0 := fun i => by have := i.2; omega
  rw [Finset.sum_eq_single j₀]
  · rw [strMat_apply, if_pos (hval j₀), if_pos (hval j₀)]
  · intro i _ hi
    exact absurd (Fin.ext ((hval i).trans (hval j₀).symm)) hi
  · intro h
    exact absurd (Finset.mem_univ _) h

end Strings
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

section Main

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem finrank_span_inf_iInf_maxGenEigenspace_eq_prod_rootMultiplicity
    (D : ℕ) (hD : D ≠ 0) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (hDQ : D.primeFactors ⊆ Q)
    (v : ↥(Nat.divisors D) → V) (hv : LinearIndependent F v)
    (U : ↥Q → Module.End F V) (a b : ↥Q → F)
    (h1 : ∀ (q : ↥Q) (d : ↥(Nat.divisors D)) (hq : (q : ℕ) ∣ (d : ℕ)),
      U q (v d) = v ⟨(d : ℕ) / q, div_mem_divisorsOn d.2 q hq⟩)
    (h2 : ∀ (q : ↥Q) (d : ↥(Nat.divisors D)), ¬ (q : ℕ) ∣ (d : ℕ) →
      U q (v d) = a q • v d - b q • (if h : (d : ℕ) * q ∣ D
        then v ⟨(d : ℕ) * q, Nat.mem_divisors.mpr ⟨h, hD⟩⟩ else 0))
    (lam : ↥Q → F) :
    Module.finrank F ↥(Submodule.span F (Set.range v) ⊓
        ⨅ q, Module.End.maxGenEigenspace (U q) (lam q)) =
      ∏ q : ↥Q, Polynomial.rootMultiplicity (lam q)
        (if D.factorization q = 0 then X - C (a q)
         else X ^ (D.factorization q - 1) * (X ^ 2 - C (a q) * X + C (b q))) := by
  classical

  let ι : ↥Q → Type := fun q => Fin (D.factorization q + 1)
  set σ : ↥(Nat.divisors D) ≃ ((q : ↥Q) → ι q) := boxEquivOn D Q hQ hDQ hD with hσ
  let Y : Submodule F V := Submodule.span F (Set.range v)
  let bY : Module.Basis ↥(Nat.divisors D) F Y := Module.Basis.span hv
  have hbY : ∀ d, (bY d : V) = v d := fun d => by rw [Module.Basis.span_apply]

  have hUv : ∀ q d, U q (v d) ∈ Y := by
    intro q d
    by_cases hqd : (q : ℕ) ∣ (d : ℕ)
    · rw [h1 q d hqd]
      exact Submodule.subset_span (Set.mem_range_self _)
    · rw [h2 q d hqd]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))
        (Submodule.smul_mem _ _ ?_)
      split_ifs
      · exact Submodule.subset_span (Set.mem_range_self _)
      · exact Submodule.zero_mem _
  have hY : ∀ q, Set.MapsTo (U q) Y Y := by
    intro q y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨d, rfl⟩
      exact hUv q d
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx

  rw [Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo U Y hY, Submodule.finrank_map_subtype_eq]

  let bY' : Module.Basis ((q : ↥Q) → ι q) F Y := bY.reindex σ
  let φ : Y ≃ₗ[F] (((q : ↥Q) → ι q) → F) := bY'.equivFun
  have hφ : ∀ d, φ (bY d) = Pi.single (σ d) (1 : F) := by
    intro d
    have : bY d = bY' (σ d) := by
      rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    rw [this]
    funext k
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  have hφsymm : ∀ j', φ.symm (Pi.single j' (1 : F)) = bY (σ.symm j') := by
    intro j'
    rw [LinearEquiv.symm_apply_eq, hφ, Equiv.apply_symm_apply]

  let T : ↥Q → Module.End F (((q : ↥Q) → ι q) → F) := fun q =>
    φ.toLinearMap ∘ₗ ((U q).restrict (hY q) ∘ₗ φ.symm.toLinearMap)
  have hT : ∀ q, φ.symm.toLinearMap ∘ₗ T q = (U q).restrict (hY q) ∘ₗ φ.symm.toLinearMap := by
    intro q
    apply LinearMap.ext
    intro x
    simp [T]
  rw [StringCountAux.finrank_iInf_maxGenEigenspace_eq_of_equiv φ.symm
    (fun q => (U q).restrict (hY q)) T hT lam]

  let Cm : (q : ↥Q) → Matrix (ι q) (ι q) F := fun q => strMat (D.factorization q) (a q) (b q)
  have hTC : ∀ q, T q = StringCountAux.coordOp ι q (Cm q) := by
    intro q
    refine (Pi.basisFun F ((q : ↥Q) → ι q)).ext fun j' => ?_
    rw [Pi.basisFun_apply, StringCountAux.coordOp_single]

    set d : ↥(Nat.divisors D) := σ.symm j' with hd
    have hjd : σ d = j' := by rw [hd, Equiv.apply_symm_apply]
    have hjq : ((j' q : ι q) : ℕ) = (d : ℕ).factorization q := by
      rw [← hjd]
      rfl

    have hTj : T q (Pi.single j' 1) = φ ((U q).restrict (hY q) (bY d)) := by
      show φ ((U q).restrict (hY q) (φ.symm (Pi.single j' 1))) = _
      rw [hφsymm]
    rw [hTj]
    by_cases hqd : (q : ℕ) ∣ (d : ℕ)
    ·
      have hpos : ((j' q : ι q) : ℕ) ≠ 0 := by
        rw [hjq]
        exact ((dvd_iff_factorization_pos hQ d q).mp hqd).ne'
      have hres : (U q).restrict (hY q) (bY d) = bY ⟨(d : ℕ) / q, div_mem_divisorsOn d.2 q hqd⟩ := by
        apply Subtype.ext
        show U q (bY d : V) = _
        rw [hbY, hbY]
        exact h1 q d hqd
      have hx : (⟨(d : ℕ).factorization q - 1,
            lt_of_le_of_lt (Nat.sub_le _ _) (boxEquivOn D Q hQ hDQ hD d q).2⟩ : ι q) =
          ⟨((j' q : ι q) : ℕ) - 1, by omega⟩ := Fin.ext (by simp [hjq])
      have hupd : σ ⟨(d : ℕ) / q, div_mem_divisorsOn d.2 q hqd⟩ =
          Function.update j' q ⟨((j' q : ι q) : ℕ) - 1, by omega⟩ := by
        funext q'
        apply Fin.ext
        rw [hσ, boxEquivOn_div hQ hDQ hD d q hqd q', hx, ← hσ, hjd]
      rw [hres, hφ, sum_strMat_smul_of_ne_zero _ _ _ _ _ hpos, hupd]
    ·
      have hzero : ((j' q : ι q) : ℕ) = 0 := by
        rw [hjq]
        exact Nat.eq_zero_of_not_pos (mt (dvd_iff_factorization_pos hQ d q).mpr hqd)
      by_cases hdq : (d : ℕ) * q ∣ D
      ·
        have he : 0 < D.factorization q := by
          have := (mul_dvd_iff_factorization_succ_le hQ d q).mp hdq
          omega
        have hres : (U q).restrict (hY q) (bY d) =
            a q • bY d - b q • bY ⟨(d : ℕ) * q, Nat.mem_divisors.mpr ⟨hdq, hD⟩⟩ := by
          apply Subtype.ext
          show U q (bY d : V) = _
          rw [hbY, h2 q d hqd, dif_pos hdq]
          simp [hbY]
        have hx : (⟨(d : ℕ).factorization q + 1,
            Nat.lt_succ_of_le ((mul_dvd_iff_factorization_succ_le hQ d q).mp hdq)⟩ : ι q) =
          ⟨1, by omega⟩ := Fin.ext (by simp [← hjq, hzero])
        have hupd : σ ⟨(d : ℕ) * q, Nat.mem_divisors.mpr ⟨hdq, hD⟩⟩ =
            Function.update j' q ⟨1, by omega⟩ := by
          funext q'
          apply Fin.ext
          rw [hσ, boxEquivOn_mul hQ hDQ hD d q hdq q', hx, ← hσ, hjd]
        rw [hres, map_sub, map_smul, map_smul, hφ, hφ, hjd,
          sum_strMat_smul_of_eq_zero_of_pos _ he _ _ _ _ hzero, Function.update_eq_self, hupd]
      ·
        have he : D.factorization q = 0 := by
          have := (mul_dvd_iff_factorization_succ_le hQ d q).not.mp hdq
          omega
        have hres : (U q).restrict (hY q) (bY d) = a q • bY d := by
          apply Subtype.ext
          show U q (bY d : V) = _
          rw [hbY, h2 q d hqd, dif_neg hdq, smul_zero, sub_zero]
          simp [hbY]
        rw [hres, map_smul, hφ, hjd, sum_strMat_smul_of_eq_zero_of_eq_zero _ he, Function.update_eq_self]

  rw [Module.End.finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update ι Cm T
    (fun q w j => by rw [hTC q]; rfl) lam]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [show (Cm q).charpoly = _ from charpoly_strMat (D.factorization q) (a q) (b q)]

end Main
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

end CESCount
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

namespace CESCount

open Module Module.End

section Generic

variable {K : Type} [Field K]

theorem comap_maxGenEigenspace_eq_of_comm
    {X Y : Type} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (j : X →ₗ[K] Y) (hj : Function.Injective j) (f' : Module.End K X) (f : Module.End K Y)
    (h : j ∘ₗ f' = f ∘ₗ j) (μ : K) :
    (f.maxGenEigenspace μ).comap j = f'.maxGenEigenspace μ := by
  have hc : ∀ y, f (j y) = j (f' y) := fun y => (LinearMap.congr_fun h y).symm
  have hk : ∀ (k : ℕ) (x : X), ((f - μ • (1 : Module.End K Y)) ^ k) (j x) =
      j (((f' - μ • (1 : Module.End K X)) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [LinearMap.sub_apply, hc]
  ext x
  simp only [Submodule.mem_comap, Module.End.mem_maxGenEigenspace, hk, map_eq_zero_iff j hj]

theorem comap_eigenspace_eq_of_comm
    {X Y : Type} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (j : X →ₗ[K] Y) (hj : Function.Injective j) (f' : Module.End K X) (f : Module.End K Y)
    (h : j ∘ₗ f' = f ∘ₗ j) (μ : K) :
    (f.eigenspace μ).comap j = f'.eigenspace μ := by
  have hc : ∀ y, f (j y) = j (f' y) := fun y => (LinearMap.congr_fun h y).symm
  ext x
  simp only [Submodule.mem_comap, Module.End.mem_eigenspace_iff, hc, ← map_smul, hj.eq_iff]

variable {A B : Type} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

theorem prodMap_sub_smul_one (f : Module.End K A) (g : Module.End K B) (μ : K) :
    f.prodMap g - μ • (1 : Module.End K (A × B)) = (f - μ • 1).prodMap (g - μ • 1) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp

theorem prodMap_pow (f : Module.End K A) (g : Module.End K B) (k : ℕ) :
    (f.prodMap g) ^ k = (f ^ k).prodMap (g ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, LinearMap.prodMap_one]
  | succ k ih => rw [pow_succ, ih, pow_succ, pow_succ, LinearMap.prodMap_mul]

theorem maxGenEigenspace_prodMap (f : Module.End K A) (g : Module.End K B) (μ : K) :
    Module.End.maxGenEigenspace (f.prodMap g) μ = (f.maxGenEigenspace μ).prod (g.maxGenEigenspace μ) := by
  ext ⟨a, b⟩
  simp only [Module.End.mem_maxGenEigenspace, Submodule.mem_prod, prodMap_sub_smul_one, prodMap_pow,
    LinearMap.prodMap_apply, Prod.mk_eq_zero]
  constructor
  · rintro ⟨k, ha, hb⟩
    exact ⟨⟨k, ha⟩, ⟨k, hb⟩⟩
  · rintro ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩⟩
    refine ⟨k₁ + k₂, ?_, ?_⟩
    · rw [add_comm, pow_add, Module.End.mul_apply, h₁, map_zero]
    · rw [pow_add, Module.End.mul_apply, h₂, map_zero]

theorem eigenspace_prodMap (f : Module.End K A) (g : Module.End K B) (μ : K) :
    Module.End.eigenspace (f.prodMap g) μ = (f.eigenspace μ).prod (g.eigenspace μ) := by
  ext ⟨a, b⟩
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_prod, LinearMap.prodMap_apply, Prod.smul_mk,
    Prod.mk.injEq]

theorem iInf_prod_iInf {ι : Type} (p : ι → Submodule K A) (q : ι → Submodule K B) :
    (⨅ i, p i).prod (⨅ i, q i) = ⨅ i, (p i).prod (q i) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_prod, Submodule.mem_iInf]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem inf_prod_inf (p p' : Submodule K A) (q q' : Submodule K B) :
    (p ⊓ p').prod (q ⊓ q') = p.prod q ⊓ p'.prod q' := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_prod, Submodule.mem_inf]
  tauto

def prodEquiv (p : Submodule K A) (q : Submodule K B) : ↥(p.prod q) ≃ₗ[K] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1, y.2), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_prod_self (p : Submodule K A) :
    Module.finrank K ↥(p.prod p) = 2 * Module.finrank K ↥p := by
  rw [LinearEquiv.finrank_eq (prodEquiv p p)]
  by_cases hfin : Module.Finite K ↥p
  · rw [Module.finrank_prod, two_mul]
  · rw [Module.finrank_of_not_finite hfin, mul_zero, Module.finrank_of_not_finite]
    intro h
    exact hfin (Module.Finite.of_surjective (LinearMap.fst K ↥p ↥p) Prod.fst_surjective)

end Generic
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

theorem range_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_map_prod
    {K : Type} [Field K] {A H : Type} [AddCommGroup A] [Module K A] [AddCommGroup H] [Module K H]
    (ES : (A × A) →ₗ[K] H) (hES : Function.Injective ES)
    {ι κ : Type} (T : ι → Module.End K H) (T' : ι → Module.End K A) (x : ι → K)
    (hT : ∀ i, T i ∘ₗ ES = ES ∘ₗ (T' i).prodMap (T' i))
    (R : κ → Module.End K H) (R' : κ → Module.End K A) (lam : κ → K)
    (hR : ∀ j, R j ∘ₗ ES = ES ∘ₗ (R' j).prodMap (R' j)) :
    LinearMap.range ES ⊓ (⨅ i, Module.End.eigenspace (T i) (x i)) ⊓
        (⨅ j, Module.End.maxGenEigenspace (R j) (lam j)) =
      Submodule.map ES
        (((⨅ i, Module.End.eigenspace (T' i) (x i)) ⊓ ⨅ j, Module.End.maxGenEigenspace (R' j) (lam j)).prod
         ((⨅ i, Module.End.eigenspace (T' i) (x i)) ⊓ ⨅ j, Module.End.maxGenEigenspace (R' j) (lam j))) := by
  rw [inf_assoc, ← Submodule.map_comap_eq, Submodule.comap_inf, Submodule.comap_iInf, Submodule.comap_iInf]
  congr 1
  rw [iInf_congr fun i => comap_eigenspace_eq_of_comm ES hES _ _ (hT i).symm (x i),
    iInf_congr fun j => comap_maxGenEigenspace_eq_of_comm ES hES _ _ (hR j).symm (lam j)]
  simp only [eigenspace_prodMap, maxGenEigenspace_prodMap, ← iInf_prod_iInf, ← inf_prod_inf]

theorem finrank_range_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul
    {K : Type} [Field K] {A H : Type} [AddCommGroup A] [Module K A] [AddCommGroup H] [Module K H]
    (ES : (A × A) →ₗ[K] H) (hES : Function.Injective ES)
    {ι κ : Type} (T : ι → Module.End K H) (T' : ι → Module.End K A) (x : ι → K)
    (hT : ∀ i, T i ∘ₗ ES = ES ∘ₗ (T' i).prodMap (T' i))
    (R : κ → Module.End K H) (R' : κ → Module.End K A) (lam : κ → K)
    (hR : ∀ j, R j ∘ₗ ES = ES ∘ₗ (R' j).prodMap (R' j)) :
    Module.finrank K ↥(LinearMap.range ES ⊓ (⨅ i, Module.End.eigenspace (T i) (x i)) ⊓
        (⨅ j, Module.End.maxGenEigenspace (R j) (lam j))) =
      2 * Module.finrank K ↥((⨅ i, Module.End.eigenspace (T' i) (x i)) ⊓
        ⨅ j, Module.End.maxGenEigenspace (R' j) (lam j)) := by
  rw [range_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_map_prod ES hES T T' x hT R R' lam hR,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ES hES _), finrank_prod_self]

theorem range_inf_maxGenEigenspace_le_eigenspace_of_prodMap
    {K : Type} [Field K] {A H : Type} [AddCommGroup A] [Module K A] [AddCommGroup H] [Module K H]
    (ES : (A × A) →ₗ[K] H) (hES : Function.Injective ES)
    (T : Module.End K H) (T' : Module.End K A) (hT : T ∘ₗ ES = ES ∘ₗ T'.prodMap T')
    (h : ∀ ν : K, Module.End.maxGenEigenspace T' ν ≤ Module.End.eigenspace T' ν) (ν : K) :
    LinearMap.range ES ⊓ Module.End.maxGenEigenspace T ν ≤ Module.End.eigenspace T ν := by
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  have hy' : y ∈ (Module.End.maxGenEigenspace T ν).comap ES := hy
  rw [comap_maxGenEigenspace_eq_of_comm ES hES _ _ hT.symm ν, maxGenEigenspace_prodMap] at hy'
  have hy'' : y ∈ (Module.End.eigenspace T ν).comap ES := by
    rw [comap_eigenspace_eq_of_comm ES hES _ _ hT.symm ν, eigenspace_prodMap]
    exact ⟨h ν hy'.1, h ν hy'.2⟩
  exact hy''

end CESCount
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

namespace CESCount

section Index

variable {α : Type} [CompleteLattice α]

theorem iInf_prop_prop_eq_iInf_subtype {P Q : ℕ → Prop} (p : (n : ℕ) → P n → Q n → α) :
    (⨅ (n : ℕ) (h₁ : P n) (h₂ : Q n), p n h₁ h₂) = ⨅ (i : {n : ℕ // P n ∧ Q n}), p i.1 i.2.1 i.2.2 := by
  apply le_antisymm
  · exact le_iInf fun i => iInf_le_of_le i.1 (iInf_le_of_le i.2.1 (iInf_le _ i.2.2))
  · exact le_iInf fun n => le_iInf fun h₁ => le_iInf fun h₂ => iInf_le_of_le ⟨n, h₁, h₂⟩ le_rfl

theorem iInf_prime_dvd_eq_iInf_primeFactors {N : ℕ} (hN : N ≠ 0) (p : (q : ℕ) → q.Prime → α) :
    (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), p q hq) =
      ⨅ (q : ↥N.primeFactors), p q (Nat.prime_of_mem_primeFactors q.2) := by
  apply le_antisymm
  · exact le_iInf fun q => iInf_le_of_le q.1 (iInf_le_of_le (Nat.prime_of_mem_primeFactors q.2)
      (iInf_le _ (Nat.dvd_of_mem_primeFactors q.2)))
  · exact le_iInf fun q => le_iInf fun hq => le_iInf fun hd =>
      iInf_le_of_le ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hd, hN⟩⟩ le_rfl

end Index
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

section CCTop

open scoped MatrixGroups

theorem mul_dvd_div_of_not_dvd {N Mg d q : ℕ} (hN : N ≠ 0) (hMgN : Mg ∣ N) (hd : d ∣ N / Mg)
    (hq : q.Prime) (hqN : q ∣ N) (hqd : ¬ q ∣ d) (hqMg : ¬ q ∣ Mg) : d * q ∣ N / Mg := by
  have hMg0 : Mg ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hMgN))
  have hD0 : N / Mg ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hMgN).mpr ⟨hN, hMg0⟩
  have hd0 : d ≠ 0 := fun h => hD0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hd0 hq.ne_zero) hD0,
    Nat.factorization_mul hd0 hq.ne_zero, hq.factorization, Nat.factorization_div hMgN]
  intro p
  rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs with hp
  · subst hp
    rw [Nat.factorization_eq_zero_of_not_dvd hqd, Nat.factorization_eq_zero_of_not_dvd hqMg, Nat.zero_add,
      Nat.sub_zero]
    exact hq.factorization_pos_of_dvd hN hqN
  · rw [Nat.add_zero, ← Finsupp.tsub_apply, ← Nat.factorization_div hMgN]
    exact (Nat.factorization_le_iff_dvd hd0 hD0).mpr hd p

end CCTop
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

end CESCount
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCount"

theorem solution
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform) (mu : ℕ → ℂ) :

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ∀ ν : ℂ,
      ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ ⊓
          Module.End.maxGenEigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) ν ≤
        Module.End.eigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) ν) ∧

    Module.finrank ℂ
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ ⊓
        (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ∉ S), Module.End.eigenspace
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) (ModularFormClass.qCoeff g ℓ)) ⊓
        (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), Module.End.maxGenEigenspace
          (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ q) (mu q))) =
    2 * ∏ q ∈ N.primeFactors, Polynomial.rootMultiplicity (mu q)
      (let e : ℕ := N.factorization q - Mg.factorization q
       if e = 0 then X - C (ModularFormClass.qCoeff g q)
       else X ^ (e - 1) * (X ^ 2 - C (ModularFormClass.qCoeff g q) * X +
         C (if q ∣ Mg then (0 : ℂ) else (q : ℂ)))) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hMg0 : Mg ≠ 0 := NeZero.ne Mg
  have hD0 : N / Mg ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hMgN).mpr ⟨hN, hMg0⟩

  obtain ⟨J, ES, -, -, hinj, hrange, hEST, hESU, -⟩ := CohCarrier.exists_eichlerShimura_H1_gammaH N ⊤

  obtain ⟨hA, v, hvdef, hvli, hvspan, hvU⟩ :=
    CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
      N S hNS Mg hMgN g hg

  let ιT : Type := {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}
  have hℓN : ∀ i : ιT, ¬ (i.1 ∣ N) := fun i h => i.2.2 (hNS i.1 i.2.1 h)
  let T : ιT → Module.End ℂ (CohCarrier.H1 N ⊤ ℂ) := fun i =>
    haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ i.1
  let T' : ιT → Module.End ℂ (CuspForm (CohCarrier.GammaH N ⊤) 2) := fun i =>
    CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 i.2.1 (hℓN i)
  let x : ιT → ℂ := fun i => ModularFormClass.qCoeff g i.1
  let R : ↥N.primeFactors → Module.End ℂ (CohCarrier.H1 N ⊤ ℂ) := fun q =>
    haveI : NeZero q.1 := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ q.1
  let R' : ↥N.primeFactors → Module.End ℂ (CuspForm (CohCarrier.GammaH N ⊤) 2) := fun q =>
    CuspForm.heckeULinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 q.1
  let lam : ↥N.primeFactors → ℂ := fun q => mu q.1

  have hT : ∀ i, T i ∘ₗ ES = ES ∘ₗ (T' i).prodMap (T' i) := by
    intro i
    apply LinearMap.ext
    rintro ⟨f₁, f₂⟩
    exact (hEST i.1 i.2.1 (hℓN i) f₁ f₂).symm
  have hR : ∀ j, R j ∘ₗ ES = ES ∘ₗ (R' j).prodMap (R' j) := by
    intro j
    apply LinearMap.ext
    rintro ⟨f₁, f₂⟩
    exact (hESU j.1 (Nat.prime_of_mem_primeFactors j.2) (Nat.dvd_of_mem_primeFactors j.2) f₁ f₂).symm
  refine ⟨?_, ?_⟩
  ·
    intro ℓ hℓ hℓN' ν
    rw [← hrange]
    exact CESCount.range_inf_maxGenEigenspace_le_eigenspace_of_prodMap ES hinj _
      (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN')
      (by apply LinearMap.ext; rintro ⟨f₁, f₂⟩; exact (hEST ℓ hℓ hℓN' f₁ f₂).symm)
      (hA ℓ hℓ hℓN') ν
  ·

    have hXT : (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S), Module.End.eigenspace
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) (ModularFormClass.qCoeff g ℓ)) =
        ⨅ i, Module.End.eigenspace (T i) (x i) :=
      CESCount.iInf_prop_prop_eq_iInf_subtype (α := Submodule ℂ (CohCarrier.H1 N ⊤ ℂ)) _
    have hXU : (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), Module.End.maxGenEigenspace
          (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ q) (mu q)) =
        ⨅ j, Module.End.maxGenEigenspace (R j) (lam j) :=
      CESCount.iInf_prime_dvd_eq_iInf_primeFactors (α := Submodule ℂ (CohCarrier.H1 N ⊤ ℂ)) hN _
    rw [← hrange, hXT, hXU,
      CESCount.finrank_range_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul ES hinj T T' x hT
        R R' lam hR]
    congr 1

    have hYT : (⨅ i, Module.End.eigenspace (T' i) (x i)) =
        Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (N / Mg)) => v (d : ℕ)) := by
      rw [hvspan]
      exact (CESCount.iInf_prop_prop_eq_iInf_subtype (α := Submodule ℂ (CuspForm (CohCarrier.GammaH N ⊤) 2))
        (fun ℓ (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) => Module.End.eigenspace
          (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ (fun h => hℓS (hNS ℓ hℓ h)))
          (ModularFormClass.qCoeff g ℓ))).symm
    rw [hYT]

    have hQ : ∀ q ∈ N.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
    have hDQ : (N / Mg).primeFactors ⊆ N.primeFactors :=
      Nat.primeFactors_mono (Nat.div_dvd_of_dvd hMgN) hN
    have hcount := CESCount.finrank_span_inf_iInf_maxGenEigenspace_eq_prod_rootMultiplicity (N / Mg) hD0 N.primeFactors
      hQ hDQ (fun d => v (d : ℕ)) hvli R' (fun q => ModularFormClass.qCoeff g q.1)
      (fun q => if (q : ℕ) ∣ Mg then (0 : ℂ) else (q : ℂ)) ?_ ?_ lam
    · rw [hcount, ← Finset.prod_attach N.primeFactors]
      refine Finset.prod_congr rfl fun q _ => ?_
      have hfac : (N / Mg).factorization q = N.factorization q - Mg.factorization q := by
        rw [Nat.factorization_div hMgN, Finsupp.tsub_apply]
      simp only [hfac]
      rfl
    ·
      intro q d hqd
      exact (hvU q.1 (hQ q q.2) (Nat.dvd_of_mem_primeFactors q.2) d (Nat.dvd_of_mem_divisors d.2)).1 hqd
    ·
      intro q d hqd
      obtain ⟨-, h2a, h2b⟩ := hvU q.1 (hQ q q.2) (Nat.dvd_of_mem_primeFactors q.2) d (Nat.dvd_of_mem_divisors d.2)
      dsimp only
      by_cases hqMg : (q : ℕ) ∣ Mg
      · rw [h2a hqd hqMg, if_pos hqMg, zero_smul, sub_zero]
      · rw [h2b hqd hqMg, if_neg hqMg, dif_pos (CESCount.mul_dvd_div_of_not_dvd hN hMgN (Nat.dvd_of_mem_divisors d.2)
          (hQ q q.2) (Nat.dvd_of_mem_primeFactors q.2) hqd hqMg)]

end S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
end P2MW
export P2MW.S_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity (solution)
