-- Prove2me | solution 1 for CerednikDrinfeld.ssFrobMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4a2ae3a3-5ea9-50f1-bf01-6f6515876f47

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_CerednikDrinfeld_exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius
import Theorems.Thm_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul
import Theorems.Thm_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_ssFrobMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

namespace D3FROBSol

theorem exists_nonsingular_fst {κ : Type} [Field κ] [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] (x : κ) :
    ∃ y, W.toAffine.Nonsingular x y := by
  set q : Polynomial κ := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X
      - Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) with hq
  have hdeg : q.degree = 2 := by
    rw [hq]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hdeg]; decide)
  refine ⟨y, (WeierstrassCurve.Affine.equation_iff_nonsingular).mp ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [hq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at hy
  linear_combination hy

theorem comp_ne_zero_of_dualPair
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₁ W W' : WeierstrassCurve κ) [X₁.IsElliptic] [W.IsElliptic] [W'.IsElliptic]
    (χ : X₁.toAffine.Point →+ W.toAffine.Point) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    (ψ : W.toAffine.Point →+ W'.toAffine.Point)
    (ψ' : W'.toAffine.Point →+ W.toAffine.Point)
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N) (h₁ : ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _) :
    ψ.comp χ ≠ 0 := by
  intro h0
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0

  have htors : ∀ Q : W.toAffine.Point, (N : ℤ) • Q = 0 := by
    intro Q
    obtain ⟨P, rfl⟩ := hsurj Q
    have h1 : ψ' (ψ (χ P)) = N • χ P := by
      simpa using DFunLike.congr_fun h₁ (χ P)
    have h2 : ψ (χ P) = 0 := DFunLike.congr_fun h0 P
    rw [h2, map_zero] at h1
    rw [natCast_zsmul]
    exact h1.symm

  have hNκ : ((N : ℕ) : κ) ≠ 0 := by
    intro h
    exact hq'N ((CharP.cast_eq_zero_iff κ q' N).mp h)
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := κ) W hNκ
  haveI : Finite (Submodule.torsionBy ℤ W.toAffine.Point N) := Finite.of_equiv _ eT.toEquiv
  have hfin : Finite W.toAffine.Point := by
    refine Finite.of_injective (fun Q => (⟨Q, ?_⟩ : Submodule.torsionBy ℤ W.toAffine.Point N)) ?_
    · rw [Submodule.mem_torsionBy_iff]; exact htors Q
    · intro Q Q' h; simpa using congrArg Subtype.val h

  have hinf : Infinite W.toAffine.Point := by
    refine Infinite.of_injective (fun x : κ => WeierstrassCurve.Affine.Point.some x (exists_nonsingular_fst W x).choose
      (exists_nonsingular_fst W x).choose_spec) ?_
    intro x x' h
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at h
    exact h.1
  exact not_finite W.toAffine.Point

end D3FROBSol

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
    (e : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' N κ))
    (he : (∀ (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (W : WeierstrassCurve κ) [W.IsElliptic]
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
        (e (ClassSet.mk (Submodule.finiteIdeleStabilizer R) x)).1.toValuationSubring =
          (moduliPlace κ N W ψ.ker).toValuationSubring.comap
            (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom))
    (data : ModularPolynomialData q') (hKr : KroneckerCongruence q' data)
    (i j : ClassSet (Submodule.finiteIdeleStabilizer R)) :
    ssFrobMatrixC q' κ N data hKr (e i) (e j) =
      classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (primeHeckeSet R q') i j := by
  haveI : DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R)) := Classical.decEq _
  have hEich : IsEichlerOrder R N := ⟨Λ₁, Submodule.conjByFiniteIdele Λ₁ m, hΛ₁, hm, hR, hRN⟩
  obtain ⟨π, hπH, hπv, -, -, -, hmat, -⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
      (Fact.out : q'.Prime) hdef hEich
  obtain ⟨hπP, hswap⟩ := QuaternionAlgebra.IsMaximalOrder.mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one q' hdef Λ₁ hΛ₁ N hq'N m hm₁ hmN hm R hR hRN π hπH hπv
  rw [hmat, Matrix.of_apply]
  unfold ssFrobMatrixC
  rw [Matrix.of_apply]
  suffices key : ∀ j : ClassSet (Submodule.finiteIdeleStabilizer R),
      frobOnPlacesGeomLevel κ N data hKr (e j).1 = (e (classSetShift _ π j)).1 by
    rw [key j]
    by_cases h : classSetShift _ π j = i
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (e.injective (Subtype.ext h')))]
  intro j

  set x := j.out with hxdef
  have hj : ClassSet.mk (Submodule.finiteIdeleStabilizer R) x = j := Quotient.out_eq j
  have hshift : classSetShift (Submodule.finiteIdeleStabilizer R) π j =
      ClassSet.mk (Submodule.finiteIdeleStabilizer R) (x * π) := rfl
  obtain ⟨W, hWE, χ, hχ, hχ0, d, hreal, W', hW'E, ψ, hψ, ψ', hψ', h1, h2, hreal2, hcyc, hcard⟩ :=
    CerednikDrinfeld.exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele q' X₁ hss a b hdef
      Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ N hq'N m hm₁ hmN hm R hR hRN x
  haveI := hWE
  haveI := hW'E
  have hex := he x W χ hχ hχ0 d hreal W' ψ hψ ψ' hψ' h1 h2 hreal2 hcyc hcard

  obtain ⟨hF, hF', ψF, ψF', hψF, hψF', hcF, hcF', h1F, h2F, hkerF⟩ :=
    WeierstrassCurve.exists_frobenius_conjugate_dualPair_mem_rationalHomSet q' W W' ψ hψ ψ' hψ' N h1 h2
  set F := WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W) with hFdef
  set F' := WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W') with hF'def
  have hχf : F.comp χ ∈ WeierstrassCurve.rationalHomSet κ X₁ (W.map (frobenius κ q')) :=
    WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W (W.map (frobenius κ q')) hχ hF
  have hFinj : Function.Injective F := by
    have h__af := (WeierstrassCurve.ratPointMap_injective (frobenius κ q') (W₀ := W))
    simp only [hFdef] at h__af ⊢
    exact h__af
  have hχf0 : F.comp χ ≠ 0 := by
    intro h0
    apply hχ0
    ext P
    have hP : F (χ P) = F 0 := by
      rw [map_zero]; exact DFunLike.congr_fun h0 P
    rw [AddMonoidHom.zero_apply]
    exact hFinj hP
  have hrealf := CerednikDrinfeld.image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ π hπv hπP x W χ hχ hχ0 d hreal
  have hψχ : ψ.comp χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W' :=
    WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W W' hχ hψ
  have hψχ0 : ψ.comp χ ≠ 0 := D3FROBSol.comp_ne_zero_of_dualPair q' X₁ W W' χ hχ hχ0 ψ ψ' N hq'N h1
  have hreal2f' := CerednikDrinfeld.image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ π hπv hπP (x * m) W' (ψ.comp χ) hψχ hψχ0 d hreal2
  have hcompeq : ψF.comp (F.comp χ) = F'.comp (ψ.comp χ) := by
    rw [← AddMonoidHom.comp_assoc, hcF, AddMonoidHom.comp_assoc]
  have hreal2f : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ (W'.map (frobenius κ q')) (ψF.comp (F.comp χ)) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * π * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
    have hk : WeierstrassCurve.kernelIdealSet κ X₁ (W'.map (frobenius κ q')) (ψF.comp (F.comp χ)) =
        WeierstrassCurve.kernelIdealSet κ X₁ (W'.map (frobenius κ q')) (F'.comp (ψ.comp χ)) :=
      congrArg _ hcompeq
    rw [hswap x]
    exact (congrArg (fun s => (⇑θ₁) '' s) hk).trans hreal2f'
  have hkerEquiv : ψ.ker ≃+ ψF.ker :=
    (AddSubgroup.equivMapOfInjective ψ.ker F hFinj).trans
      (AddEquiv.addSubgroupCongr hkerF.symm)
  have hcycF : IsAddCyclic ψF.ker := by
    haveI := hcyc
    exact isAddCyclic_of_surjective hkerEquiv.toAddMonoidHom hkerEquiv.surjective
  have hcardF : Nat.card ψF.ker = N := by
    rw [← hcard]; exact (Nat.card_congr hkerEquiv.toEquiv).symm
  have hexf := he (x * π) (W.map (frobenius κ q')) (F.comp χ) hχf hχf0 d hrealf (W'.map (frobenius κ q'))
    ψF hψF ψF' hψF' h1F h2F hreal2f hcycF hcardF

  have hA := ModularCurve.frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius q' N hq'N data hKr W ψ.ker hcyc hcard (e (ClassSet.mk _ x)).1 (hj ▸ hex)
  rw [hshift, ← hj]
  apply Place.ext
  rw [hA, hexf, hkerF]

end S_CerednikDrinfeld_ssFrobMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace
end P2MW
export P2MW.S_CerednikDrinfeld_ssFrobMatrixC_apply_eq_classSetHeckeMatrix_primeHeckeSet_of_forall_toValuationSubring_eq_comap_moduliPlace (solution)
