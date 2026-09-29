-- Prove2me | solution 1 for CerednikDrinfeld.autOnPlaces_eq_of_isAtkinLehnerLevelAut_of_forall_toValuationSubring_eq_comap_moduliPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4bc186f9-31b0-5909-9ea8-af86b863ee78

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_CerednikDrinfeld_exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele
import Theorems.Thm_CerednikDrinfeld_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_and_exists_dualPair_ker_eq_map_of_meetOrder_eq_of_conjByFiniteIdele_eq
import Theorems.Thm_WeierstrassCurve_exists_rationalHom_ker_eq_zmultiples_toValuationSubring_autOnPlaces_eq_comap_moduliPlace_map_sup_ker_nsmul
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_autOnPlaces_eq_of_isAtkinLehnerLevelAut_of_forall_toValuationSubring_eq_comap_moduliPlace
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

namespace Ws47
namespace K5Glue

theorem addOrderOf_div_nsmul {G : Type*} [AddCommGroup G] {g : G} {N e : ℕ} (hg : addOrderOf g = N) (hN : N ≠ 0)
    (he : e ∣ N) : addOrderOf ((N / e) • g) = e := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he (Nat.pos_of_ne_zero hN)
  have hq : 0 < N / e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) he) he0
  rw [addOrderOf_nsmul' _ hq.ne', hg, Nat.gcd_eq_right (Nat.div_dvd_of_dvd he), Nat.div_div_self he hN]

theorem exists_mem_addOrderOf_eq {G : Type*} [AddCommGroup G] (C : AddSubgroup G) {n e : ℕ}
    (hC : IsAddCyclic C) (hn : Nat.card C = n) (hn0 : n ≠ 0) (he : e ∣ n) :
    ∃ Q ∈ C, addOrderOf Q = e := by
  haveI := hC
  obtain ⟨⟨g, hg⟩, hgen⟩ := IsAddCyclic.exists_generator (α := C)
  have hord : addOrderOf g = n := by
    rw [← hn, ← Nat.card_zmultiples]
    congr 1
    refine congrArg _ (le_antisymm (AddSubgroup.zmultiples_le.mpr hg) fun y hy => ?_)
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen ⟨y, hy⟩)
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨z, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  exact ⟨(n / e) • g, C.nsmul_mem hg _, addOrderOf_div_nsmul hord hn0 he⟩

end Ws47.K5Glue

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
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hSn : S = meetOrder R n) (hnorm : Submodule.conjByFiniteIdele S n = S)
    (hM : jqNModC κ N ∈ modularFunctionFieldC κ (N * q)) (hSq : jqNModC κ q ∈ modularFunctionFieldC κ (N * q))
    (σ : ↥(modularFunctionFieldC κ (N * q)) ≃ₐ[κ] ↥(modularFunctionFieldC κ (N * q)))
    (hσ : IsAtkinLehnerLevelAut κ N q hM hSq σ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (eE (ClassSet.mk (Submodule.finiteIdeleStabilizer S) (x * n))).1 =
      autOnPlaces κ N q σ (eE (ClassSet.mk (Submodule.finiteIdeleStabilizer S) x)).1 := by
  classical
  have hqP : (q : ℕ).Prime := Fact.out
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) hqP.ne_zero⟩

  obtain ⟨W, hW, χ, hχ, hχ0, d, hK, W', hW', ψ, hψ, ψ', hψ', hψ'ψ, hψψ', hKJ, hcyc, hcard⟩ :=
    CerednikDrinfeld.exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁
      hθ₁ hθ₁Λ (N * q) hq'q m' hm'₁ hm'N hm' S hS hSlvl x

  obtain ⟨Q, hQC, hQ⟩ := Ws47.K5Glue.exists_mem_addOrderOf_eq ψ.ker hcyc hcard (NeZero.ne (N * q)) (Dvd.intro_left N rfl)

  obtain ⟨E', hE', φ, hφ, hφker, -, hφuniv, hAL⟩ :=
    WeierstrassCurve.exists_rationalHom_ker_eq_zmultiples_toValuationSubring_autOnPlaces_eq_comap_moduliPlace_map_sup_ker_nsmul
      q' N q hqP hqN hq'q hM hSq σ hσ W ψ.ker hcyc hcard Q hQC hQ

  obtain ⟨hφχ0, hK1, V', hV', ρ, hρ, ρ', hρ', hρ'ρ, hρρ', hK2, hρker, hρcyc, hρcard⟩ :=
    CerednikDrinfeld.image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_and_exists_dualPair_ker_eq_map_of_meetOrder_eq_of_conjByFiniteIdele_eq
      q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ N hq'N m hm₁ hmN hm R hR hRN q hqN hq'q m' hm'₁ hm'N hm' S hS hSlvl n hn hSn hnorm
      x W χ hχ hχ0 d hK W' ψ hψ ψ' hψ' hψ'ψ hψψ' hKJ hcyc hcard Q hQC hQ E' φ hφ hφker hφuniv

  have hx := heE x W χ hχ hχ0 d hK W' ψ hψ ψ' hψ' hψ'ψ hψψ' hKJ hcyc hcard
  have hφχ : φ.comp χ ∈ WeierstrassCurve.rationalHomSet κ X₁ E' :=
    WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W E' hχ hφ
  have hxn := heE (x * n) E' (φ.comp χ) hφχ hφχ0 d hK1 V' ρ hρ ρ' hρ' hρ'ρ hρρ' hK2 hρcyc hρcard

  apply Place.ext
  rw [hxn, hAL _ hx, hρker]

end S_CerednikDrinfeld_autOnPlaces_eq_of_isAtkinLehnerLevelAut_of_forall_toValuationSubring_eq_comap_moduliPlace
end P2MW
export P2MW.S_CerednikDrinfeld_autOnPlaces_eq_of_isAtkinLehnerLevelAut_of_forall_toValuationSubring_eq_comap_moduliPlace (solution)
