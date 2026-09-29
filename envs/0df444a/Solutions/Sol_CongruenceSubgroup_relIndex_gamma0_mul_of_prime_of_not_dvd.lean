-- Prove2me | solution 1 for CongruenceSubgroup.relIndex_gamma0_mul_of_prime_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/bea5f0b5-1a67-502c-9253-b17e26192cfe

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_card_quotient_gamma0_eq_index
import Theorems.Thm_ModularCurve_card_quotient_gamma0_le_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_relIndex_gamma0_mul_of_prime_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open ModularCurve IntermediateField CongruenceSubgroup
open scoped MatrixGroups

namespace IndexAtom

theorem Gamma0_le_of_dvd (M : ℕ) {N : ℕ} (h : N ∣ M) : Gamma0 M ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hA

theorem index_gamma0_eq_dedekindPsi (N : ℕ) [NeZero N] : (Gamma0 N).index = dedekindPsi N := by
  haveI : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_in_Gamma0 N)
  have hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (Gamma0 N) :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  let x : ↥(qExpFunctionFieldC ℚ (Gamma0 N)) := ⟨jqModC ℚ, hj⟩
  have hT : ModularGroup.T ∈ Gamma0 N := by rw [Gamma0_mem]; simp [ModularGroup.T]
  obtain ⟨hfd, hle⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (Gamma0 N) hT
    (Gamma0 N) le_rfl (fun γ h => Or.inl h) x rfl
  haveI := hfd
  have hlow := ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 ℚ N (NeZero.natCast_ne N ℚ) x rfl
  have hidx : (Gamma0 N).index ≤ dedekindPsi N := by
    rw [← ModularCurve.card_quotient_gamma0_eq_index N]
    exact ModularCurve.card_quotient_gamma0_le_dedekindPsi N
  exact le_antisymm hidx (hlow.trans hle)

end IndexAtom

open IndexAtom in
theorem solution
    (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) :
    (CongruenceSubgroup.Gamma0 (N * p)).relIndex (CongruenceSubgroup.Gamma0 N) = p + 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (N * p) := ⟨Nat.mul_ne_zero (NeZero.ne N) hp.ne_zero⟩
  have hle : Gamma0 (N * p) ≤ Gamma0 N := Gamma0_le_of_dvd (N * p) (Dvd.intro p rfl)
  have hmul := Subgroup.relIndex_mul_index hle
  rw [index_gamma0_eq_dedekindPsi, index_gamma0_eq_dedekindPsi, ModularCurve.dedekindPsi_mul_prime N p hp, if_neg hpN] at hmul
  have hψ : 0 < dedekindPsi N := by
    rw [← index_gamma0_eq_dedekindPsi]
    haveI : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_in_Gamma0 N)
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  exact Nat.eq_of_mul_eq_mul_right hψ hmul

end S_CongruenceSubgroup_relIndex_gamma0_mul_of_prime_of_not_dvd
end P2MW
export P2MW.S_CongruenceSubgroup_relIndex_gamma0_mul_of_prime_of_not_dvd (solution)
