-- Prove2me | solution 1 for CuspForm.exists_not_dvd_and_algInt_qExpansion_smul_alSlash_diamond_of_mem_twoCuspIntegralSet_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/554368e9-1d61-5ede-ba3e-406af65ee067

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularForm_exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_not_dvd_and_algInt_qExpansion_smul_alSlash_diamond_of_mem_twoCuspIntegralSet_of_ker_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup

namespace TwoCuspALPIntKerLe

theorem one_mem_strictPeriods_Gamma1 (M : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ Gamma1 M := by
    rw [Gamma1_mem]
    simp [ModularGroup.T]
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem exists_isIntegralQExp_diamondLinH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (e : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ pf : PowerSeries ℤ, ModularCurve.IsIntegralQExp (⇑(CuspForm.diamondLinH 2 e f)) pf := by
  obtain ⟨W₀⟩ := ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd
    (M := M) (q := p) Fact.out hpM hpM2
  have hmem : (CuspForm.diamondLinH 2 e : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] _) ∈
      CuspForm.heckeRingH M H 2 := by
    have h := CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) 2 (CohCarrier.Gen.dia e)
    rwa [CuspForm.heckeGenH_dia] at h
  have hint : ∀ n : ℕ, ∃ a : ℤ,
      (a : ℂ) = ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 e f)) n := fun n =>
    Subring.mem_bot.mp (hf _ hmem W₀ n).1
  choose a ha using hint
  refine ⟨PowerSeries.mk a, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, ha n]
  rfl

end TwoCuspALPIntKerLe

end

open TwoCuspALPIntKerLe in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ D : ℕ, ¬ p ∣ D ∧ ∃ pfW : PowerSeries ↥(integralClosure ℤ ℂ),
      pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
        UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) := by

  obtain ⟨pf, hpf⟩ := exists_isIntegralQExp_diamondLinH p M H hpM hpM2 e f hf

  set F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2 :=
    ((CuspForm.diamondLinH 2 e f : CuspForm (CohCarrier.GammaH M H) 2) :
      ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2) with hF
  have hFcoe : (⇑F : UpperHalfPlane → ℂ) = ⇑(CuspForm.diamondLinH 2 e f) := rfl

  obtain ⟨D, hpD, hD⟩ :=
    ModularForm.exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even p M H
      hpM hpM2 hHp Wd (k := 2) ⟨1, rfl⟩ F pf (by rw [hFcoe]; exact hpf)
  rw [hFcoe] at hD

  obtain ⟨g, hg⟩ := CuspForm.exists_gamma1_coe_eq_alSlash_diamondLinH p M H hpM hpM2 Wd e f hf
  refine ⟨D, hpD, PowerSeries.mk fun n =>
    ⟨(D : ℂ) * (UpperHalfPlane.qExpansion 1
      (ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))).coeff n,
      (mem_integralClosure_iff ℤ ℂ).mpr (hD n)⟩, ?_⟩
  have hsmul : UpperHalfPlane.qExpansion 1
      ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) =
      (D : ℂ) • UpperHalfPlane.qExpansion 1 (ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) := by
    rw [← hg]
    exact UpperHalfPlane.qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos (one_mem_strictPeriods_Gamma1 M)) (D : ℂ)
  rw [hsmul]
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul]
  rfl

end S_CuspForm_exists_not_dvd_and_algInt_qExpansion_smul_alSlash_diamond_of_mem_twoCuspIntegralSet_of_ker_le
end P2MW
export P2MW.S_CuspForm_exists_not_dvd_and_algInt_qExpansion_smul_alSlash_diamond_of_mem_twoCuspIntegralSet_of_ker_le (solution)
