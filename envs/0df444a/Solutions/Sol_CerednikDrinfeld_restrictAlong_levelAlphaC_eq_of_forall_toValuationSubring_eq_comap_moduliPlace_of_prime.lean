-- Prove2me | solution 1 for CerednikDrinfeld.restrictAlong_levelAlphaC_eq_of_forall_toValuationSubring_eq_comap_moduliPlace_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b6ffc4b8-e455-5c6e-bd3b-7a8f8fee0135

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_inclusion
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_ModularCurve_isModuliPlaceOf_nonempty
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
import Theorems.Thm_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime

import Theorems.Thm_CerednikDrinfeld_exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_restrictAlong_levelAlphaC_eq_of_forall_toValuationSubring_eq_comap_moduliPlace_of_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld ModularCurve AlgebraicCurve"

namespace WsEleven
namespace C3

theorem restrictAlong_levelAlphaC_eq_of_toValuationSubring_eq
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (N q : ℕ) [NeZero N] [NeZero q] (hq'N : ¬ q' ∣ N) (hq'q : ¬ q' ∣ N * q)
    (hM : jqNModC κ N ∈ modularFunctionFieldC κ (N * q))
    (hA : (levelAlphaC κ N q hM).toRingHom.IsIntegral)
    (W : WeierstrassCurve κ) (KE K : AddSubgroup W.toAffine.Point)
    (hKE : IsAddCyclic KE ∧ Nat.card KE = N * q) (hK : IsAddCyclic K ∧ Nat.card K = N)
    (hsub : ∀ T ∈ KE, (N * q / N) • T ∈ K)
    (vE : Place κ ↥(modularFunctionFieldC κ (N * q))) (vV : Place κ ↥(modularFunctionFieldC κ N))
    (hE : vE.toValuationSubring = (moduliPlace κ (N * q) W KE).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).toRingHom)
    (hV : vV.toValuationSubring = (moduliPlace κ N W K).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    Place.restrictAlong (levelAlphaC κ N q hM) hA vE = vV := by
  have hdvd : N ∣ N * q := Dvd.intro q rfl
  haveI : NeZero q' := ⟨(Fact.out : q'.Prime).ne_zero⟩
  have hNq : ((N * q : ℕ) : κ) ≠ 0 := fun h => hq'q ((CharP.cast_eq_zero_iff κ q' (N * q)).mp h)
  have hN0 : ((N : ℕ) : κ) ≠ 0 := fun h => hq'N ((CharP.cast_eq_zero_iff κ q' N).mp h)

  have heq : modularFunctionFieldC κ (N * q) = modularFunctionFieldFullC κ (N * q) :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos κ q' (N * q) hq'q
  have hsurj : Function.Surjective (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))) := by
    intro y
    refine ⟨⟨y.1, ?_⟩, rfl⟩
    rw [heq]; exact y.2
  have hIfull : (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ hsurj
  have h1 : ((IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).comp
      (levelAlphaC κ N q hM)).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hA hIfull
  have key : (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).comp (levelAlphaC κ N q hM) =
      (IntermediateField.inclusion (full_degeneracyC_le κ hdvd)).comp
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)) := by
    apply AlgHom.ext
    intro f
    rfl
  have h2 : ((IntermediateField.inclusion (full_degeneracyC_le κ hdvd)).comp
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N))).toRingHom.IsIntegral := key ▸ h1
  have hincl : (IntermediateField.inclusion (full_degeneracyC_le κ hdvd)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.tower_top _ _ h2
  have hα : (moduliPlace κ (N * q) W KE).restrictAlong
      (IntermediateField.inclusion (full_degeneracyC_le κ hdvd)) hincl = moduliPlace κ N W K :=
    moduliPlace_restrictAlong_inclusion κ (N * q) N hdvd
      (fun y => isModuliPlaceOf_nonempty κ (N * q) hNq y)
      (fun y v v' hv hv' => eq_of_isModuliPlaceOf κ N hN0 y v v' hv hv') hincl W ⟨KE, hKE⟩ ⟨K, hK⟩ hsub
  apply Place.ext
  rw [hV, ← hα]
  change vE.toValuationSubring.comap (levelAlphaC κ N q hM).toRingHom =
    ((moduliPlace κ (N * q) W KE).toValuationSubring.comap
      (IntermediateField.inclusion (full_degeneracyC_le κ hdvd)).toRingHom).comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom
  rw [hE, ValuationSubring.comap_comap, ValuationSubring.comap_comap]
  exact congrArg ((moduliPlace κ (N * q) W KE).toValuationSubring.comap ·) (congrArg AlgHom.toRingHom key)

section Adelic
variable {a b : ℚ}

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add u w _ _ hu hw => rw [add_mul]; exact add_mem hu hw
    | neg u _ hu =>
      convert neg_mem hu using 1
      exact neg_mul u _
  | zero => rw [mul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mul_add]; exact add_mem hu hw
  | neg u _ hu =>
    convert neg_mem hu using 1
    exact mul_neg x u

theorem ofFiniteIdele_le_of_inv_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g g' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (h : ((g⁻¹ * g' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.ofFiniteIdele Λ g' ≤ Submodule.ofFiniteIdele Λ g := by
  intro z hz
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨((g⁻¹ * g' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) * w, mul_mem_finiteAdeleBox hΛ h hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← hwz, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]

theorem smul_mem_ofFiniteIdele_of_smul_inv_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g g' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (c : ℚ)
    (h : c • ((g'⁻¹ * g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ g) : c • z ∈ Submodule.ofFiniteIdele Λ g' := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨(c • ((g'⁻¹ * g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))) * w, mul_mem_finiteAdeleBox hΛ h hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [smul_mul_assoc, mul_smul_comm, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left, hwz,
    TensorProduct.smul_tmul']

end Adelic

theorem exists_nsmul_subgroup {G : Type*} [AddCommGroup G] (K : AddSubgroup G) (N q : ℕ) [NeZero N] [NeZero q]
    (hK : IsAddCyclic K) (hcard : Nat.card K = N * q) :
    ∃ H : AddSubgroup G, IsAddCyclic H ∧ Nat.card H = N ∧ (∀ T ∈ K, q • T ∈ H) ∧
      (∀ P ∈ H, ∃ T ∈ K, P = q • T) := by
  obtain ⟨g, hg⟩ := hK.exists_generator
  have hog : addOrderOf (g : G) = N * q := by
    rw [AddSubgroup.addOrderOf_coe, addOrderOf_eq_card_of_forall_mem_zmultiples hg, hcard]
  refine ⟨AddSubgroup.zmultiples (q • (g : G)), inferInstance, ?_, ?_, ?_⟩
  · have hfin : IsOfFinAddOrder (g : G) := by
      rw [← addOrderOf_pos_iff, hog]; exact Nat.pos_of_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne q))
    rw [Nat.card_zmultiples, IsOfFinAddOrder.addOrderOf_nsmul (g : G) q hfin, hog,
      Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne q))]
  · intro T hT
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨T, hT⟩)
    have hk' : (k • (g : G)) = T := by
      have := congrArg (fun u : K => (u : G)) hk
      simpa using this
    rw [← hk', ← smul_comm]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) k
  · intro P hP
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
    exact ⟨k • (g : G), K.zsmul_mem g.2 k, (smul_comm q k (g : G)).symm⟩

theorem nsmul_id_mem_rationalHomSet (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) :
    (n • AddMonoidHom.id (W.baseChange k).toAffine.Point) ∈ WeierstrassCurve.rationalHomSet k W W := by
  induction n with
  | zero =>
    have h0 : (0 : ℕ) • AddMonoidHom.id (W.baseChange k).toAffine.Point = 0 := by ext P; simp
    rw [h0]; exact WeierstrassCurve.zero_mem_rationalHomSet k W W
  | succ n ih =>
    have hs : (n + 1) • AddMonoidHom.id (W.baseChange k).toAffine.Point =
        n • AddMonoidHom.id (W.baseChange k).toAffine.Point + AddMonoidHom.id _ := by ext P; simp [succ_nsmul]
    rw [hs]
    exact WeierstrassCurve.add_mem_rationalHomSet k W W ih (WeierstrassCurve.id_mem_rationalHomSet k W)

end WsEleven.C3

open WsEleven.C3 in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (q : ℕ) [NeZero q] [Fact q.Prime] (hqN : ¬ q ∣ N) (hq'q : ¬ q' ∣ N * q)
    (m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm'₁ : ((m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'N : ((N * q : ℕ) : ℚ) • ((m'⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm' : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m'))
    (S : Submodule ℤ ℍ[ℚ, a, b]) (hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m')
    (hSlvl : S.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N * q)
    (hmm' : ((m⁻¹ * m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hqm'm : ((q : ℕ) : ℚ) • ((m'⁻¹ * m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (eV : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' N κ))
    (heV : (∀ (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (W : WeierstrassCurve κ) [W.IsElliptic]
        (χ : X₁.toAffine.Point →+ W.toAffine.Point), χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W → χ ≠ 0 →
        ∀ d : (ℍ[ℚ, a, b])ˣ, θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
          star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) →
        ∀ (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point),
          ψ ∈ WeierstrassCurve.rationalHomSet κ W W' →
        ∀ (ψ' : W'.toAffine.Point →+ W.toAffine.Point), ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W →
          ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _ → ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _ →
        θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
          star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) →
        IsAddCyclic ψ.ker → Nat.card ψ.ker = N →
        (eV (ClassSet.mk (Submodule.finiteIdeleStabilizer R) x)).1.toValuationSubring =
          (moduliPlace κ N W ψ.ker).toValuationSubring.comap
            (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom))
    (eE : ClassSet (Submodule.finiteIdeleStabilizer S) ≃ ↥(ssPlaces q' (N * q) κ))
    (heE : (∀ (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (W : WeierstrassCurve κ) [W.IsElliptic]
        (χ : X₁.toAffine.Point →+ W.toAffine.Point), χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W → χ ≠ 0 →
        ∀ d : (ℍ[ℚ, a, b])ˣ, θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
          star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) →
        ∀ (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point),
          ψ ∈ WeierstrassCurve.rationalHomSet κ W W' →
        ∀ (ψ' : W'.toAffine.Point →+ W.toAffine.Point), ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W →
          ψ'.comp ψ = ((N * q) : ℕ) • AddMonoidHom.id _ → ψ.comp ψ' = ((N * q) : ℕ) • AddMonoidHom.id _ →
        θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
          star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) →
        IsAddCyclic ψ.ker → Nat.card ψ.ker = (N * q) →
        (eE (ClassSet.mk (Submodule.finiteIdeleStabilizer S) x)).1.toValuationSubring =
          (moduliPlace κ (N * q) W ψ.ker).toValuationSubring.comap
            (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).toRingHom))
    (hM : jqNModC κ N ∈ modularFunctionFieldC κ (N * q))
    (hA : (levelAlphaC κ N q hM).toRingHom.IsIntegral)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Place.restrictAlong (levelAlphaC κ N q hM) hA (eE (ClassSet.mk (Submodule.finiteIdeleStabilizer S) x)).1 =
      (eV (ClassSet.mk (Submodule.finiteIdeleStabilizer R) x)).1 := by
  classical
  have hNq0 : ((N * q : ℕ) : κ) ≠ 0 := fun h => hq'q ((CharP.cast_eq_zero_iff κ q' (N * q)).mp h)
  have hN0 : ((N : ℕ) : κ) ≠ 0 := fun h => hq'N ((CharP.cast_eq_zero_iff κ q' N).mp h)

  obtain ⟨W, hW, χ, hχ, hχ0, d, hKx, W'', hW'', ψE, hψE, ψE', hψE', hψE'ψE, hψEψE', hKxE, hcycE, hcardE⟩ :
      ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic) (χ : X₁.toAffine.Point →+ W.toAffine.Point)
        (_ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (_ : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
        (_ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
          star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
        (W' : WeierstrassCurve κ) (_ : W'.IsElliptic) (ψ : W.toAffine.Point →+ W'.toAffine.Point)
        (_ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
        (ψ' : W'.toAffine.Point →+ W.toAffine.Point) (_ : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
        (_ : ψ'.comp ψ = ((N * q : ℕ) : ℕ) • AddMonoidHom.id _) (_ : ψ.comp ψ' = ((N * q : ℕ) : ℕ) • AddMonoidHom.id _)
        (_ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
          star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])),
        IsAddCyclic ψ.ker ∧ Nat.card ψ.ker = N * q :=
    CerednikDrinfeld.exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele q' X₁ hss a b hdef Λ₁ hΛ₁
      θ₁ hθ₁ hθ₁Λ (N * q) hq'q m' hm'₁ hm'N hm' S hS hSlvl x
  haveI := hW; haveI := hW''

  obtain ⟨H, hHcyc, hHcard, hHsub, hHmem⟩ := exists_nsmul_subgroup ψE.ker N q hcycE hcardE

  have hHκ : ((Nat.card H : ℕ) : κ) ≠ 0 := by rw [hHcard]; exact hN0
  obtain ⟨V, hV, π, hπ, hπsurj, hπker, hπuniv⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp W H hHκ
  haveI := hV

  have hHN : H ≤ ((N : ℕ) • AddMonoidHom.id W.toAffine.Point).ker := by
    intro P hP
    rw [AddMonoidHom.mem_ker, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, ← hHcard]
    have := card_nsmul_eq_zero' (x := (⟨P, hP⟩ : H))
    exact congrArg Subtype.val this
  obtain ⟨π', hπ', hππ'eq⟩ := hπuniv W ((N : ℕ) • AddMonoidHom.id _) (nsmul_id_mem_rationalHomSet κ W N)
    (hπker ▸ hHN)
  have hπ'π : π'.comp π = (N : ℕ) • AddMonoidHom.id _ := hππ'eq.symm
  have hππ' : π.comp π' = (N : ℕ) • AddMonoidHom.id _ := by
    ext Q
    obtain ⟨P, rfl⟩ := hπsurj Q
    rw [AddMonoidHom.comp_apply, show π' (π P) = (π'.comp π) P from rfl, hπ'π, AddMonoidHom.nsmul_apply,
      AddMonoidHom.id_apply, map_nsmul, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]

  have hqdiv : N * q / N = q := Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))
  have hπker' : ∀ T : W.toAffine.Point, T ∈ π.ker ↔ ∃ S ∈ ψE.ker, (N * q / N) • S = T := by
    intro T
    rw [hπker, hqdiv]
    exact ⟨fun h => by obtain ⟨S, hS, e⟩ := hHmem T h; exact ⟨S, hS, e.symm⟩, fun ⟨S, hS, e⟩ => e ▸ hHsub S hS⟩
  have hcyc : IsAddCyclic π.ker := by rw [hπker]; exact hHcyc
  have hcard : Nat.card π.ker = N := by rw [hπker]; exact hHcard
  have hsub : ∀ T ∈ ψE.ker, (N * q / N) • T ∈ π.ker := fun T hT => (hπker' _).mpr ⟨T, hT, rfl⟩

  have hcop : Nat.Coprime N (N * q / N) := by
    rw [hqdiv]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqN).symm
  have hKxm : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V (π.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) :=
    CerednikDrinfeld.image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ x W χ hχ hχ0 d hKx (N * q) hq'q m' W'' ψE hψE ψE' hψE' hψE'ψE hψEψE'
      hKxE N (Dvd.intro q rfl) hcop m hm₁ hmm' hmN (by rw [hqdiv]; exact hqm'm) V π hπ hπker'
      (fun V' _ α hα hle => hπuniv V' α hα (hπker ▸ hle))

  have hE := heE x W χ hχ hχ0 d hKx W'' ψE hψE ψE' hψE' hψE'ψE hψEψE' hKxE hcycE hcardE
  have hV := heV x W χ hχ hχ0 d hKx V π hπ π' hπ' hπ'π hππ' hKxm hcyc hcard

  exact restrictAlong_levelAlphaC_eq_of_toValuationSubring_eq q' N q hq'N hq'q hM hA W ψE.ker π.ker
    ⟨hcycE, hcardE⟩ ⟨hcyc, hcard⟩ hsub _ _ hE hV

end S_CerednikDrinfeld_restrictAlong_levelAlphaC_eq_of_forall_toValuationSubring_eq_comap_moduliPlace_of_prime
end P2MW
export P2MW.S_CerednikDrinfeld_restrictAlong_levelAlphaC_eq_of_forall_toValuationSubring_eq_comap_moduliPlace_of_prime (solution)
