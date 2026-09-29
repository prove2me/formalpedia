-- Prove2me | solution 1 for CerednikDrinfeld.exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/929837bd-fd33-5e4f-81cd-e5325814de16

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld IsDedekindDomain"

noncomputable section

namespace CerednikDrinfeld
namespace KernelIdealDescent
p2m_open "CerednikDrinfeld"

section Points

open Polynomial WeierstrassCurve

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

theorem infinite_point (W : WeierstrassCurve F) [IsAlgClosed k] [W.IsElliptic] : Infinite (Pt k W) := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hy : ∀ x : k, ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y := by
    intro x
    have hdeg : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
        WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ((W.baseChange k).toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [IsRoot.def, map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : Pt k W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

variable [DecidableEq k]
variable {W₁ W₂ : WeierstrassCurve F}

theorem sub_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂)
    (hβ : β ∈ rationalHomSet k W₁ W₂) : α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet k W₁ W₂ hβ)

theorem zsmul_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (c : ℤ) :
    c • α ∈ rationalHomSet k W₁ W₂ := by
  induction c using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih => rw [add_zsmul, one_zsmul]; exact add_mem_rationalHomSet k W₁ W₂ ih hα
  | pred n ih => rw [sub_zsmul, one_zsmul]; exact sub_mem_rationalHomSet ih hα

theorem nsmul_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (c : ℕ) :
    c • α ∈ rationalHomSet k W₁ W₂ := by
  rw [← natCast_zsmul]; exact zsmul_mem_rationalHomSet hα c

theorem eq_zero_of_finite_range [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (hfin : (Set.range α).Finite) :
    α = 0 := by
  by_contra hα0
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hα hα0
  haveI := infinite_point (k := k) W₂
  rw [hsurj.range_eq] at hfin
  exact Set.infinite_univ hfin

theorem finite_torsion [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : n ≠ 0)
    (hnk : (n : k) ≠ 0) : {P : Pt k W | (n : ℤ) • P = 0}.Finite := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt k W) (n : ℤ)) = n ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hnk
  haveI : Finite (Submodule.torsionBy ℤ (Pt k W) (n : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]; exact pow_ne_zero 2 hn
  have : {P : Pt k W | (n : ℤ) • P = 0} = ((Submodule.torsionBy ℤ (Pt k W) (n : ℤ)) : Set (Pt k W)) := by
    ext P; exact (Submodule.mem_torsionBy_iff _ _).symm
  rw [this]
  exact Set.toFinite _

theorem eq_zero_of_nsmul_eq_zero [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) {n : ℕ} (hn : n ≠ 0)
    (hnk : (n : k) ≠ 0) (h : n • α = 0) : α = 0 := by
  refine eq_zero_of_finite_range hα ((finite_torsion W₂ hn hnk).subset ?_)
  rintro _ ⟨P, rfl⟩
  have := DFunLike.congr_fun h P
  rw [AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply] at this
  change (n : ℤ) • α P = 0
  rw [natCast_zsmul]; exact this

theorem exists_ne_zero_smul_eq_zero [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) :
    ∃ Q : Pt k W, Q ≠ 0 ∧ (ℓ : ℤ) • Q = 0 := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hℓk
  haveI : Finite (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]; exact pow_ne_zero 2 hℓ.ne_zero
  have hnt : Nontrivial (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hℓ.one_lt
  obtain ⟨⟨Q, hQ⟩, hQ0⟩ := exists_ne (0 : Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ))
  refine ⟨Q, fun h => hQ0 (Subtype.ext h), ?_⟩
  exact (Submodule.mem_torsionBy_iff _ _).mp hQ

theorem smul_id_ne_zero [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    (n • AddMonoidHom.id (Pt k W)) ≠ 0 := by
  intro hzero
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (max n.natAbs (ringChar k) + 1)
  have hℓn : n.natAbs < ℓ := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hℓle
  have hℓc : ringChar k < ℓ := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right _ _)) hℓle
  have hℓk : (ℓ : k) ≠ 0 := by
    intro h0
    have hdvd : ringChar k ∣ ℓ := (CharP.cast_eq_zero_iff k (ringChar k) ℓ).mp h0
    rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h2
    · exact CharP.ringChar_ne_one h1
    · exact absurd h2 hℓc.ne
  obtain ⟨Q, hQ0, hQℓ⟩ := exists_ne_zero_smul_eq_zero (k := k) W hℓ hℓk
  have hQn : n • Q = 0 := by
    have := DFunLike.congr_fun hzero Q
    rwa [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at this
  have hnd : ¬ (ℓ : ℤ) ∣ n := by
    intro hd
    rw [Int.natCast_dvd] at hd
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd) (not_le.mpr hℓn)
  have hcop : IsCoprime (ℓ : ℤ) n :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ).irreducible).mpr hnd
  obtain ⟨a, b, hab⟩ := hcop
  apply hQ0
  calc Q = (a * (ℓ : ℤ) + b * n) • Q := by rw [hab, one_smul]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, hQℓ, hQn, smul_zero, smul_zero, add_zero]

end Points

section Quaternion

variable {a b : ℚ}

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) :
    star h ∈ Λ := by
  obtain ⟨-, t, ht⟩ := hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hh
  have e : star h = ((trd h : ℚ) : ℍ[ℚ, a, b]) - h := by
    rw [← add_star_eq_coe_trd]; abel
  have e2 : ((trd h : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, coe_intCast, zsmul_eq_mul, mul_one]
  rw [e, e2]
  exact Λ.sub_mem (Λ.smul_mem t hΛ.one_mem) hh

theorem coe_units_smul (e : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) :
    ((e • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = (fun z => (e : ℍ[ℚ, a, b]) * z) '' (I : Set ℍ[ℚ, a, b]) := by
  ext z
  erw [Submodule.mem_smul_pointwise_iff_exists]

theorem mem_units_smul_iff (e : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) :
    z ∈ (e • I : Submodule ℤ ℍ[ℚ, a, b]) ↔ ((e⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z ∈ I := by
  rw [← SetLike.mem_coe, coe_units_smul, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩

end Quaternion

section Adelic

variable {a b : ℚ}

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ}
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

theorem tmul_one_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, 1, fun v => one_mem _, rfl⟩

theorem mul_mem_ofFiniteIdele {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {z μ : ℍ[ℚ, a, b]}
    (hz : z ∈ Submodule.ofFiniteIdele Λ g) (hμ : μ ∈ Λ) : z * μ ∈ Submodule.ofFiniteIdele Λ g := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨w * μ ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ), mul_mem_finiteAdeleBox hΛ hw (tmul_one_mem_finiteAdeleBox hμ), ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← mul_assoc, hwz, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem ofFiniteIdele_mul_le_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.finiteAdeleBox Λ) :
    Submodule.ofFiniteIdele Λ (x * g) ≤ Submodule.ofFiniteIdele Λ x := by
  intro z hz
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨(g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * w, mul_mem_finiteAdeleBox hΛ hg hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← mul_assoc]
  exact hwz

end Adelic

section Frame

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}

def homGrp (W X₀ : WeierstrassCurve κ) [W.IsElliptic] [X₀.IsElliptic] : AddSubgroup (Pt κ W →+ Pt κ X₀) where
  carrier := rationalHomSet κ W X₀
  zero_mem' := zero_mem_rationalHomSet κ W X₀
  add_mem' ha hb := add_mem_rationalHomSet κ W X₀ ha hb
  neg_mem' ha := neg_mem_rationalHomSet κ W X₀ ha

variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]

theorem mem_homGrp {ρ : Pt κ W →+ Pt κ X₀} : ρ ∈ homGrp W X₀ ↔ ρ ∈ rationalHomSet κ W X₀ := Iff.rfl

theorem closure_rationalHomSet : AddSubgroup.closure (rationalHomSet κ W X₀) = homGrp W X₀ :=
  le_antisymm ((AddSubgroup.closure_le _).mpr fun _ h => h) fun _ h => AddSubgroup.subset_closure h

structure IsLatticeFrame (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (χ : Pt κ X₀ →+ Pt κ W) (d : (ℍ[ℚ, a, b])ˣ)
    (J₀ : Submodule ℤ ℍ[ℚ, a, b]) : Prop where
  isOrder : IsOrder Λ
  inj : Function.Injective θ
  range_eq : Set.range θ = (Λ : Set ℍ[ℚ, a, b])
  mem : χ ∈ rationalHomSet κ X₀ W
  ne_zero : χ ≠ 0
  ker_eq : θ '' (kernelIdealSet κ X₀ W χ) = star '' ((d • J₀ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])

def compEnd {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (ρ : homGrp W X₀) :
    ↥(rationalEndSubring κ X₀) :=
  ⟨(ρ.1).comp χ, Subring.subset_closure (comp_mem_rationalHomSet κ X₀ W X₀ hχ ρ.2)⟩

@[scoped simp] theorem coe_compEnd {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (ρ : homGrp W X₀) :
    ((compEnd hχ ρ : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt κ X₀)) = (ρ.1).comp χ := rfl

theorem compEnd_mem_kernelIdealSet {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (ρ : homGrp W X₀) :
    compEnd hχ ρ ∈ kernelIdealSet κ X₀ W χ := ⟨ρ.1, ρ.2, rfl⟩

def tr (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) : homGrp W X₀ →+ ℍ[ℚ, a, b] where
  toFun ρ := ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star (θ (compEnd hχ ρ))
  map_zero' := by
    have : compEnd hχ (0 : homGrp W X₀) = 0 := Subtype.ext (by ext P; rfl)
    rw [this, map_zero, star_zero, mul_zero]
  map_add' ρ ρ' := by
    have : compEnd hχ (ρ + ρ') = compEnd hχ ρ + compEnd hχ ρ' := Subtype.ext (by ext P; rfl)
    rw [this, map_add, star_add, mul_add]

theorem tr_apply (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) (ρ : homGrp W X₀) :
    tr θ hχ d ρ = ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star (θ (compEnd hχ ρ)) := rfl

theorem theta_compEnd_eq (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (ρ : homGrp W X₀) :
    θ (compEnd hχ ρ) = star ((d : ℍ[ℚ, a, b]) * tr θ hχ d ρ) := by
  rw [tr_apply, ← mul_assoc, Units.mul_inv, one_mul, star_star]

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]} {χ : Pt κ X₀ →+ Pt κ W}
  {d : (ℍ[ℚ, a, b])ˣ} {J₀ : Submodule ℤ ℍ[ℚ, a, b]}

theorem IsLatticeFrame.compEnd_injective (hF : IsLatticeFrame Λ θ χ d J₀) : Function.Injective (compEnd hF.mem) := by
  intro ρ ρ' h
  have h2 := congrArg (fun e : ↥(rationalEndSubring κ X₀) => (e : AddMonoid.End (Pt κ X₀))) h
  simp only [coe_compEnd] at h2
  apply Subtype.ext
  ext Q
  obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hF.mem hF.ne_zero Q
  exact DFunLike.congr_fun h2 P

theorem IsLatticeFrame.tr_injective (hF : IsLatticeFrame Λ θ χ d J₀) : Function.Injective (tr θ hF.mem d) := by
  intro ρ ρ' h
  rw [tr_apply, tr_apply] at h
  have h1 := star_injective ((Units.mul_right_inj _).mp h)
  exact hF.compEnd_injective (hF.inj h1)

theorem IsLatticeFrame.range_tr (hF : IsLatticeFrame Λ θ χ d J₀) :
    Set.range (tr θ hF.mem d) = (J₀ : Set ℍ[ℚ, a, b]) := by
  ext z
  constructor
  · rintro ⟨ρ, rfl⟩
    have h1 : θ (compEnd hF.mem ρ) ∈ θ '' (kernelIdealSet κ X₀ W χ) := ⟨_, compEnd_mem_kernelIdealSet hF.mem ρ, rfl⟩
    rw [hF.ker_eq] at h1
    obtain ⟨w, hw, hw'⟩ := h1
    rw [SetLike.mem_coe, mem_units_smul_iff] at hw
    rw [SetLike.mem_coe, tr_apply, ← hw', star_star]
    exact hw
  · intro hz
    have h1 : star ((d : ℍ[ℚ, a, b]) * z) ∈ θ '' (kernelIdealSet κ X₀ W χ) := by
      rw [hF.ker_eq]
      refine ⟨(d : ℍ[ℚ, a, b]) * z, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_units_smul_iff, ← mul_assoc, Units.inv_mul, one_mul]
      exact hz
    obtain ⟨e, ⟨ρ, hρ, he⟩, he'⟩ := h1
    refine ⟨⟨ρ, hρ⟩, ?_⟩
    have : compEnd hF.mem ⟨ρ, hρ⟩ = e := Subtype.ext (by rw [coe_compEnd, he])
    rw [tr_apply, this, he', star_star, ← mul_assoc, Units.inv_mul, one_mul]

theorem IsLatticeFrame.tr_mem (hF : IsLatticeFrame Λ θ χ d J₀) (ρ : homGrp W X₀) :
    tr θ hF.mem d ρ ∈ J₀ := by
  rw [← SetLike.mem_coe, ← hF.range_tr]; exact ⟨ρ, rfl⟩

theorem IsLatticeFrame.exists_tr_eq (hF : IsLatticeFrame Λ θ χ d J₀) {z : ℍ[ℚ, a, b]} (hz : z ∈ J₀) :
    ∃ ρ : homGrp W X₀, tr θ hF.mem d ρ = z := by
  have : z ∈ Set.range (tr θ hF.mem d) := by rw [hF.range_tr]; exact hz
  exact this

theorem tr_comp {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (d : (ℍ[ℚ, a, b])ˣ) (α : ↥(rationalEndSubring κ X₀)) (ρ : homGrp W X₀)
    (hαρ : ((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ.1 ∈ rationalHomSet κ W X₀) :
    tr θ hχ d ⟨((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ.1, hαρ⟩ = tr θ hχ d ρ * star (θ α) := by
  have : compEnd hχ ⟨((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp ρ.1, hαρ⟩ = α * compEnd hχ ρ :=
    Subtype.ext (by ext P; rfl)
  rw [tr_apply, tr_apply, this, map_mul, star_mul, mul_assoc]

def ann (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (U : AddSubgroup (Pt κ W)) : AddSubgroup (Pt κ W →+ Pt κ X₀) where
  carrier := {ρ | ρ ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.ker}
  zero_mem' := ⟨zero_mem_rationalHomSet κ W X₀, fun _ _ => rfl⟩
  add_mem' {u v} hu hv := ⟨add_mem_rationalHomSet κ W X₀ hu.1 hv.1, fun P hP => by
    change (u + v) P = 0
    rw [AddMonoidHom.add_apply, show u P = 0 from hu.2 hP, show v P = 0 from hv.2 hP, add_zero]⟩
  neg_mem' {u} hu := ⟨neg_mem_rationalHomSet κ W X₀ hu.1, fun P hP => by
    change (-u) P = 0
    rw [AddMonoidHom.neg_apply, show u P = 0 from hu.2 hP, neg_zero]⟩

theorem mem_ann {U : AddSubgroup (Pt κ W)} {ρ : Pt κ W →+ Pt κ X₀} :
    ρ ∈ ann X₀ U ↔ ρ ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.ker := Iff.rfl

def modOf (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) : AddSubgroup (Pt κ W →+ Pt κ X₀) :=
  ((J.toAddSubgroup).comap (tr θ hχ d)).map (homGrp W X₀).subtype

theorem mem_modOf_iff (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) (ρ : Pt κ W →+ Pt κ X₀) :
    ρ ∈ modOf θ hχ d J ↔ ∃ h : ρ ∈ rationalHomSet κ W X₀, tr θ hχ d ⟨ρ, h⟩ ∈ J := by
  unfold modOf
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ'.2, hρ'⟩
  · rintro ⟨h, hJ⟩
    exact ⟨⟨ρ, h⟩, hJ, rfl⟩

theorem modOf_le_homGrp (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) :
    modOf θ hχ d J ≤ homGrp W X₀ := fun ρ h => ((mem_modOf_iff θ hχ d J ρ).mp h).1

def jker (ℓ : ℕ) (M : AddSubgroup (Pt κ W →+ Pt κ X₀)) : AddSubgroup (Pt κ W) where
  carrier := {P | (ℓ : ℤ) • P = 0 ∧ ∀ μ ∈ M, μ P = 0}
  zero_mem' := ⟨smul_zero _, fun μ _ => map_zero μ⟩
  add_mem' {P Q} hP hQ := ⟨by rw [smul_add, hP.1, hQ.1, add_zero], fun μ hμ => by rw [map_add, hP.2 μ hμ, hQ.2 μ hμ, add_zero]⟩
  neg_mem' {P} hP := ⟨by rw [smul_neg, hP.1, neg_zero], fun μ hμ => by rw [map_neg, hP.2 μ hμ, neg_zero]⟩

theorem mem_jker {ℓ : ℕ} {M : AddSubgroup (Pt κ W →+ Pt κ X₀)} {P : Pt κ W} :
    P ∈ jker ℓ M ↔ (ℓ : ℤ) • P = 0 ∧ ∀ μ ∈ M, μ P = 0 := Iff.rfl

theorem natCard_jker_cast_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0) (M : AddSubgroup (Pt κ W →+ Pt κ X₀)) :
    ((Nat.card (jker (X₀ := X₀) ℓ M) : ℕ) : κ) ≠ 0 := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt κ W) (ℓ : ℤ)) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W hℓκ
  have hle : jker (X₀ := X₀) ℓ M ≤ (Submodule.torsionBy ℤ (Pt κ W) (ℓ : ℤ)).toAddSubgroup := by
    intro P hP
    exact (Submodule.mem_torsionBy_iff _ _).mpr hP.1
  have hdvd : Nat.card (jker (X₀ := X₀) ℓ M) ∣ ℓ ^ 2 := by
    rw [← hcard]
    exact AddSubgroup.card_dvd_of_le hle
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
  rw [hi, Nat.cast_pow]
  exact pow_ne_zero i hℓκ

theorem IsLatticeFrame.exists_ne_zero (hF : IsLatticeFrame Λ θ χ d J₀) : ∃ σ ∈ rationalHomSet κ W X₀, σ ≠ 0 := by
  obtain ⟨σ, hσ, n, hn, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₀ W hF.mem hF.ne_zero
  refine ⟨σ, hσ, fun h0 => smul_id_ne_zero (k := κ) X₀ hn.ne' ?_⟩
  ext P
  rw [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, ← hdual.comp_left P, h0,
    AddMonoidHom.zero_apply]

theorem IsLatticeFrame.dictB (hF : IsLatticeFrame Λ θ χ d J₀) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    (M : AddSubgroup (Pt κ W →+ Pt κ X₀)) (hMH : (M : Set _) ⊆ rationalHomSet κ W X₀)
    (hMℓ : ∀ ρ ∈ rationalHomSet κ W X₀, ℓ • ρ ∈ M)
    (hMR : ∀ α ∈ rationalHomSet κ X₀ X₀, ∀ ρ ∈ M, α.comp ρ ∈ M)
    (ρ : Pt κ W →+ Pt κ X₀) (hρ : ρ ∈ rationalHomSet κ W X₀)
    (hρK : ∀ P : Pt κ W, (ℓ : ℤ) • P = 0 → (∀ μ ∈ M, μ P = 0) → ρ P = 0) : ρ ∈ M :=
  (WeierstrassCurve.relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero X₀ a b Λ
    hF.isOrder θ hF.inj hF.range_eq W hF.exists_ne_zero ℓ hℓ hℓκ).2 M hMH hMℓ hMR ρ hρ hρK

end Frame

section Step

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]
variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]}
  {χ : Pt κ X₀ →+ Pt κ W} {d : (ℍ[ℚ, a, b])ˣ} {J₀ : Submodule ℤ ℍ[ℚ, a, b]}

theorem nsmul_id_ne_zero (W : WeierstrassCurve κ) [W.IsElliptic] {ℓ : ℕ} (hℓ : ℓ ≠ 0) (hℓκ : (ℓ : κ) ≠ 0) :
    (ℓ • AddMonoidHom.id (Pt κ W)) ≠ 0 := by
  intro h
  have h0 := eq_zero_of_nsmul_eq_zero (id_mem_rationalHomSet κ W) hℓ hℓκ h
  haveI := infinite_point (k := κ) W
  obtain ⟨P, hP⟩ := exists_ne (0 : Pt κ W)
  exact hP (by simpa using DFunLike.congr_fun h0 P)

theorem IsLatticeFrame.modOf_props (hF : IsLatticeFrame Λ θ χ d J₀) {ℓ : ℕ} {J : Submodule ℤ ℍ[ℚ, a, b]}
    (hJ2 : ∀ z ∈ J₀, (ℓ : ℤ) • z ∈ J) (hJmul : ∀ z ∈ J, ∀ μ ∈ Λ, z * μ ∈ J) :
    ((modOf θ hF.mem d J : Set (Pt κ W →+ Pt κ X₀)) ⊆ rationalHomSet κ W X₀) ∧
    (∀ ρ ∈ rationalHomSet κ W X₀, ℓ • ρ ∈ modOf θ hF.mem d J) ∧
    (∀ α ∈ rationalHomSet κ X₀ X₀, ∀ ρ ∈ modOf θ hF.mem d J, α.comp ρ ∈ modOf θ hF.mem d J) := by
  refine ⟨fun ρ h => modOf_le_homGrp θ hF.mem d J h, fun ρ hρ => ?_, fun α hα ρ hρM => ?_⟩
  · refine (mem_modOf_iff θ hF.mem d J _).mpr ⟨nsmul_mem_rationalHomSet hρ ℓ, ?_⟩
    have : (⟨ℓ • ρ, nsmul_mem_rationalHomSet hρ ℓ⟩ : homGrp W X₀) = ℓ • ⟨ρ, hρ⟩ := Subtype.ext rfl
    rw [this, map_nsmul, ← natCast_zsmul]
    exact hJ2 _ (hF.tr_mem _)
  · obtain ⟨hρ, hJ⟩ := (mem_modOf_iff θ hF.mem d J ρ).mp hρM
    have hαρ : α.comp ρ ∈ rationalHomSet κ W X₀ := comp_mem_rationalHomSet κ W X₀ X₀ hρ hα
    refine (mem_modOf_iff θ hF.mem d J _).mpr ⟨hαρ, ?_⟩
    let α' : ↥(rationalEndSubring κ X₀) := ⟨α, Subring.subset_closure hα⟩
    have hα'Λ : θ α' ∈ Λ := by
      rw [← SetLike.mem_coe, ← hF.range_eq]; exact ⟨α', rfl⟩
    have := tr_comp hF.mem θ d α' ⟨ρ, hρ⟩ hαρ
    change tr θ hF.mem d ⟨α.comp ρ, hαρ⟩ = _ at this
    rw [this]
    exact hJmul _ hJ _ (star_mem_of_mem hF.isOrder hα'Λ)

theorem IsLatticeFrame.ann_jker_modOf (hF : IsLatticeFrame Λ θ χ d J₀) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    {J : Submodule ℤ ℍ[ℚ, a, b]}
    (hJ2 : ∀ z ∈ J₀, (ℓ : ℤ) • z ∈ J) (hJmul : ∀ z ∈ J, ∀ μ ∈ Λ, z * μ ∈ J) :
    ann X₀ (jker ℓ (modOf θ hF.mem d J)) = modOf θ hF.mem d J := by
  obtain ⟨hMH, hMℓ, hMR⟩ := hF.modOf_props (ℓ := ℓ) hJ2 hJmul
  ext ρ
  constructor
  · rintro ⟨hρ, hU⟩
    exact hF.dictB hℓ hℓκ _ hMH hMℓ hMR ρ hρ fun P hP hM => hU (show P ∈ jker ℓ _ from ⟨hP, hM⟩)
  · intro hρM
    exact ⟨hMH hρM, fun P hP => hP.2 ρ hρM⟩

theorem IsLatticeFrame.image_kernelIdealSet_quotient (hF : IsLatticeFrame Λ θ χ d J₀) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓκ : (ℓ : κ) ≠ 0) {J : Submodule ℤ ℍ[ℚ, a, b]} (hJ1 : J ≤ J₀)
    (hJ2 : ∀ z ∈ J₀, (ℓ : ℤ) • z ∈ J) (hJmul : ∀ z ∈ J, ∀ μ ∈ Λ, z * μ ∈ J)
    {V : WeierstrassCurve κ} [V.IsElliptic] {π : Pt κ W →+ Pt κ V} (hπ : π ∈ rationalHomSet κ W V)
    (hπker : π.ker = jker ℓ (modOf θ hF.mem d J))
    (huniv : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : Pt κ W →+ Pt κ V'),
      α ∈ rationalHomSet κ W V' → jker ℓ (modOf θ hF.mem d J) ≤ α.ker → ∃ β ∈ rationalHomSet κ V V', α = β.comp π) :
    θ '' (kernelIdealSet κ X₀ V (π.comp χ)) = star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  have hann := hF.ann_jker_modOf hℓ hℓκ hJ2 hJmul
  ext w
  constructor
  · rintro ⟨e, ⟨ρ', hρ', he⟩, rfl⟩
    have hρ : ρ'.comp π ∈ rationalHomSet κ W X₀ := comp_mem_rationalHomSet κ W V X₀ hπ hρ'
    have hρU : ρ'.comp π ∈ ann X₀ (jker ℓ (modOf θ hF.mem d J)) := ⟨hρ, fun P hP => by
      rw [← hπker] at hP
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, show π P = 0 from hP, map_zero]⟩
    rw [hann] at hρU
    obtain ⟨h, hJ⟩ := (mem_modOf_iff θ hF.mem d J _).mp hρU
    have hce : compEnd hF.mem ⟨ρ'.comp π, h⟩ = e := Subtype.ext (by rw [coe_compEnd, he]; rfl)
    refine ⟨(d : ℍ[ℚ, a, b]) * tr θ hF.mem d ⟨ρ'.comp π, h⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_units_smul_iff, ← mul_assoc, Units.inv_mul, one_mul]; exact hJ
    · rw [← theta_compEnd_eq, hce]
  · rintro ⟨w', hw', rfl⟩
    rw [SetLike.mem_coe, mem_units_smul_iff] at hw'
    obtain ⟨ρ, hρ⟩ := hF.exists_tr_eq (hJ1 hw')
    have hρM : ρ.1 ∈ modOf θ hF.mem d J := (mem_modOf_iff θ hF.mem d J ρ.1).mpr ⟨ρ.2, by rw [hρ]; exact hw'⟩
    rw [← hann] at hρM
    obtain ⟨ρV, hρV, hρeq⟩ := huniv X₀ ρ.1 ρ.2 hρM.2
    refine ⟨compEnd hF.mem ρ, ⟨ρV, hρV, by rw [coe_compEnd, hρeq]; rfl⟩, ?_⟩
    rw [theta_compEnd_eq θ hF.mem d ρ, hρ, ← mul_assoc, Units.mul_inv, one_mul]

theorem IsLatticeFrame.step (hF : IsLatticeFrame Λ θ χ d J₀) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    {J : Submodule ℤ ℍ[ℚ, a, b]} (hJ1 : J ≤ J₀)
    (hJ2 : ∀ z ∈ J₀, (ℓ : ℤ) • z ∈ J) (hJmul : ∀ z ∈ J, ∀ μ ∈ Λ, z * μ ∈ J) :
    ∃ (V : WeierstrassCurve κ) (_ : V.IsElliptic) (ψ : Pt κ W →+ Pt κ V) (_ : ψ ∈ rationalHomSet κ W V)
      (ψ' : Pt κ V →+ Pt κ W) (_ : ψ' ∈ rationalHomSet κ V W),
      Function.Surjective ψ ∧ IsLatticeFrame Λ θ (ψ.comp χ) d J ∧
      ψ'.comp ψ = Nat.card ψ.ker • AddMonoidHom.id _ ∧ ψ.comp ψ' = Nat.card ψ.ker • AddMonoidHom.id _ := by
  set U := jker ℓ (modOf θ hF.mem d J) with hUdef

  have hUκ : ((Nat.card U : ℕ) : κ) ≠ 0 := natCard_jker_cast_ne_zero hℓ hℓκ _
  obtain ⟨V, hV, π, hπ, hπs, hπker, huniv⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp W U hUκ
  haveI := hV
  have hπχ : π.comp χ ∈ rationalHomSet κ X₀ V := comp_mem_rationalHomSet κ X₀ W V hF.mem hπ

  have hUkill : U ≤ ((Nat.card U : ℕ) • AddMonoidHom.id (Pt κ W)).ker := by
    intro P hP
    rw [AddMonoidHom.mem_ker, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]
    have h := card_nsmul_eq_zero' (x := (⟨P, hP⟩ : U))
    exact congrArg Subtype.val h
  obtain ⟨πd, hπd, hπdeq⟩ := huniv W ((Nat.card U : ℕ) • AddMonoidHom.id _)
    (nsmul_mem_rationalHomSet (id_mem_rationalHomSet κ W) _) hUkill

  have hπχ0 : π.comp χ ≠ 0 := by
    intro h0
    have hs := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hF.mem hF.ne_zero
    have hπ0 : π = 0 := by
      ext Q
      obtain ⟨P, rfl⟩ := hs Q
      exact DFunLike.congr_fun h0 P
    haveI := infinite_point (k := κ) V
    obtain ⟨Q, hQ⟩ := exists_ne (0 : Pt κ V)
    obtain ⟨P, rfl⟩ := hπs Q
    exact hQ (by rw [hπ0, AddMonoidHom.zero_apply])

  have hKER := hF.image_kernelIdealSet_quotient hℓ hℓκ hJ1 hJ2 hJmul hπ hπker huniv

  have hππd : π.comp πd = (Nat.card U : ℕ) • AddMonoidHom.id _ := by
    ext Q
    obtain ⟨P, rfl⟩ := hπs Q
    change π (πd (π P)) = ((Nat.card U : ℕ) • AddMonoidHom.id (Pt κ V)) (π P)
    rw [show πd (π P) = (πd.comp π) P from rfl, ← hπdeq, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, map_nsmul,
      AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]
  refine ⟨V, hV, π, hπ, πd, hπd, hπs, ⟨hF.isOrder, hF.inj, hF.range_eq, hπχ, hπχ0, hKER⟩, ?_, ?_⟩
  · rw [hπker]; exact hπdeq.symm
  · rw [hπker]; exact hππd

end Step

section KerComp

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

theorem natCard_ker_comp (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker := by
  set K' : AddSubgroup A := g.ker.comap f with hK'
  have hcomp : (g.comp f).ker = K' := (AddMonoidHom.comap_ker g f).symm
  have hle : f.ker ≤ K' := by
    intro x hx
    rw [hK', AddSubgroup.mem_comap, AddMonoidHom.mem_ker, show f x = 0 from hx, map_zero]
  have h1 : Nat.card (f.ker.addSubgroupOf K') * (f.ker.addSubgroupOf K').index = Nat.card K' :=
    AddSubgroup.card_mul_index _
  have h2 : Nat.card (f.ker.addSubgroupOf K') = Nat.card f.ker :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
  have h3 : (f.ker.addSubgroupOf K').index = Nat.card g.ker := by
    change f.ker.relIndex K' = Nat.card g.ker
    rw [← AddMonoidHom.comap_bot, AddSubgroup.relIndex_comap, hK', AddSubgroup.map_comap_eq_self_of_surjective hf,
      AddSubgroup.relIndex_bot_left]
  rw [hcomp, ← h1, h2, h3]

end KerComp

section Descent

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₀ : WeierstrassCurve κ} [X₀.IsElliptic]
variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]} {d : (ℍ[ℚ, a, b])ˣ}

def scaled (n : ℤ) (J₀ : Submodule ℤ ℍ[ℚ, a, b]) : Submodule ℤ ℍ[ℚ, a, b] :=
  J₀.map (n • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b]))

omit [IsAlgClosed κ] [DecidableEq κ] in
theorem mem_scaled_iff {n : ℤ} {J₀ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} :
    z ∈ scaled n J₀ ↔ ∃ y ∈ J₀, n • y = z := by
  unfold scaled
  rw [Submodule.mem_map]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]

theorem descend (L : List ℕ) (hL : ∀ ℓ ∈ L, ℓ.Prime ∧ (ℓ : κ) ≠ 0) :
    ∀ (W : WeierstrassCurve κ) [W.IsElliptic] (χ : Pt κ X₀ →+ Pt κ W) (J₀ : Submodule ℤ ℍ[ℚ, a, b]),
      IsLatticeFrame Λ θ χ d J₀ → (∀ z ∈ J₀, ∀ μ ∈ Λ, z * μ ∈ J₀) →
      ∀ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ J₀ → (∀ z ∈ J, ∀ μ ∈ Λ, z * μ ∈ J) →
        (∀ z ∈ J₀, ((L.prod : ℕ) : ℤ) • z ∈ J) →
        ∃ (V : WeierstrassCurve κ) (_ : V.IsElliptic) (ψ : Pt κ W →+ Pt κ V) (_ : ψ ∈ rationalHomSet κ W V)
          (ψ' : Pt κ V →+ Pt κ W) (_ : ψ' ∈ rationalHomSet κ V W),
          Function.Surjective ψ ∧
          θ '' (kernelIdealSet κ X₀ V (ψ.comp χ)) = star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∧
          ψ'.comp ψ = Nat.card ψ.ker • AddMonoidHom.id _ ∧ ψ.comp ψ' = Nat.card ψ.ker • AddMonoidHom.id _ := by
  induction L with
  | nil =>
    intro W _ χ J₀ hF hJ₀mul J hJ1 hJmul hprod

    have hJ : J = J₀ := by
      refine le_antisymm hJ1 fun z hz => ?_
      have := hprod z hz
      rwa [List.prod_nil, Nat.cast_one, one_smul] at this
    subst hJ
    refine ⟨W, inferInstance, AddMonoidHom.id _, id_mem_rationalHomSet κ W, AddMonoidHom.id _, id_mem_rationalHomSet κ W,
      Function.surjective_id, ?_, ?_, ?_⟩
    · rw [AddMonoidHom.id_comp]; exact hF.ker_eq
    · rw [AddMonoidHom.ker_id, AddSubgroup.card_bot, one_smul]; rfl
    · rw [AddMonoidHom.ker_id, AddSubgroup.card_bot, one_smul]; rfl
  | cons ℓ L' ih =>
    intro W _ χ J₀ hF hJ₀mul J hJ1 hJmul hprod
    obtain ⟨hℓ, hℓκ⟩ := hL ℓ (List.mem_cons_self)
    have hL' : ∀ ℓ' ∈ L', ℓ'.Prime ∧ (ℓ' : κ) ≠ 0 := fun ℓ' h => hL ℓ' (List.mem_cons_of_mem ℓ h)

    set J₁ : Submodule ℤ ℍ[ℚ, a, b] := J ⊔ scaled (ℓ : ℤ) J₀ with hJ₁def
    have hJJ₁ : J ≤ J₁ := le_sup_left
    have hJ₁J₀ : J₁ ≤ J₀ := by
      refine sup_le hJ1 fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := mem_scaled_iff.mp hz
      exact J₀.smul_mem _ hy
    have hJ₁2 : ∀ z ∈ J₀, (ℓ : ℤ) • z ∈ J₁ := fun z hz =>
      Submodule.mem_sup_right (mem_scaled_iff.mpr ⟨z, hz, rfl⟩)
    have hJ₁mul : ∀ z ∈ J₁, ∀ μ ∈ Λ, z * μ ∈ J₁ := by
      intro z hz μ hμ
      obtain ⟨j, hj, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨y, hy, rfl⟩ := mem_scaled_iff.mp hw
      rw [add_mul, smul_mul_assoc]
      exact Submodule.add_mem _ (hJJ₁ (hJmul j hj μ hμ)) (hJ₁2 _ (hJ₀mul y hy μ hμ))
    have hprod' : ∀ z ∈ J₁, ((L'.prod : ℕ) : ℤ) • z ∈ J := by
      intro z hz
      obtain ⟨j, hj, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨y, hy, rfl⟩ := mem_scaled_iff.mp hw
      rw [smul_add, smul_smul]
      refine J.add_mem (J.smul_mem _ hj) ?_
      have := hprod y hy
      rw [List.prod_cons, Nat.cast_mul] at this
      rwa [mul_comm]

    obtain ⟨V₁, hV₁, ψ₁, hψ₁, ψ₁', hψ₁', hψ₁s, hF₁, h₁l, h₁r⟩ := hF.step hℓ hℓκ hJ₁J₀ hJ₁2 hJ₁mul
    haveI := hV₁

    obtain ⟨V, hV, ψ₂, hψ₂, ψ₂', hψ₂', hψ₂s, hK, h₂l, h₂r⟩ := ih hL' V₁ (ψ₁.comp χ) J₁ hF₁ hJ₁mul J hJJ₁ hJmul hprod'
    haveI := hV

    set n₁ := Nat.card ψ₁.ker with hn₁
    set n₂ := Nat.card ψ₂.ker with hn₂
    have hn : Nat.card (ψ₂.comp ψ₁).ker = n₁ * n₂ := natCard_ker_comp ψ₁ ψ₂ hψ₁s
    refine ⟨V, hV, ψ₂.comp ψ₁, comp_mem_rationalHomSet κ W V₁ V hψ₁ hψ₂, ψ₁'.comp ψ₂',
      comp_mem_rationalHomSet κ V V₁ W hψ₂' hψ₁', hψ₂s.comp hψ₁s, ?_, ?_, ?_⟩
    · rw [AddMonoidHom.comp_assoc]; exact hK
    · rw [hn]
      ext P
      change ψ₁' (ψ₂' (ψ₂ (ψ₁ P))) = ((n₁ * n₂) • AddMonoidHom.id (Pt κ W)) P
      rw [show ψ₂' (ψ₂ (ψ₁ P)) = (ψ₂'.comp ψ₂) (ψ₁ P) from rfl, h₂l, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply,
        map_nsmul, show ψ₁' (ψ₁ P) = (ψ₁'.comp ψ₁) P from rfl, h₁l, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply,
        AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, smul_smul, mul_comm]
    · rw [hn]
      ext Q
      change ψ₂ (ψ₁ (ψ₁' (ψ₂' Q))) = ((n₁ * n₂) • AddMonoidHom.id (Pt κ V)) Q
      rw [show ψ₁ (ψ₁' (ψ₂' Q)) = (ψ₁.comp ψ₁') (ψ₂' Q) from rfl, h₁r, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply,
        map_nsmul, show ψ₂ (ψ₂' Q) = (ψ₂.comp ψ₂') Q from rfl, h₂r, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply,
        AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, smul_smul]

end Descent

end CerednikDrinfeld.KernelIdealDescent
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld.KernelIdealDescent"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld.KernelIdealDescent"

open CerednikDrinfeld.KernelIdealDescent WeierstrassCurve in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hgq' : ¬ q' ∣ (Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup) :
    ∃ (W' : WeierstrassCurve κ) (_ : W'.IsElliptic) (ψ : W.toAffine.Point →+ W'.toAffine.Point)
      (_ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W') (ψ' : W'.toAffine.Point →+ W.toAffine.Point)
      (_ : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W),
      θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * g) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∧
      ψ'.comp ψ = Nat.card ψ.ker • AddMonoidHom.id _ ∧ ψ.comp ψ' = Nat.card ψ.ker • AddMonoidHom.id _ := by

  have hF : IsLatticeFrame (X₀ := X₁) (W := W) Λ₁ θ₁ (χ : Pt κ X₁ →+ Pt κ W) d (Submodule.ofFiniteIdele Λ₁ x) :=
    ⟨hΛ₁.isOrder, hθ₁, hθ₁Λ, hχ, hχ0, hK⟩
  set J₀ := Submodule.ofFiniteIdele Λ₁ x with hJ₀def
  set J := Submodule.ofFiniteIdele Λ₁ (x * g) with hJdef
  have hJ1 : J ≤ J₀ := ofFiniteIdele_mul_le_of_mem hΛ₁.isOrder x g hg
  have hJ₀mul : ∀ z ∈ J₀, ∀ μ ∈ Λ₁, z * μ ∈ J₀ := fun z hz μ hμ => mul_mem_ofFiniteIdele hΛ₁.isOrder _ hz hμ
  have hJmul : ∀ z ∈ J, ∀ μ ∈ Λ₁, z * μ ∈ J := fun z hz μ hμ => mul_mem_ofFiniteIdele hΛ₁.isOrder _ hz hμ

  set m := J.toAddSubgroup.relIndex J₀.toAddSubgroup with hmdef
  have hm0 : m ≠ 0 := by
    intro h0
    exact hgq' (by rw [h0]; exact dvd_zero _)
  set L := m.primeFactorsList with hLdef
  have hL : ∀ ℓ ∈ L, ℓ.Prime ∧ (ℓ : κ) ≠ 0 := by
    intro ℓ hℓL
    have hℓ : ℓ.Prime := Nat.prime_of_mem_primeFactorsList hℓL
    refine ⟨hℓ, fun h => ?_⟩
    have hd : q' ∣ ℓ := (CharP.cast_eq_zero_iff κ q' ℓ).mp h
    have hℓq : ℓ = q' := ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hℓ).mp hd).symm
    exact hgq' (by rw [← hℓq]; exact Nat.dvd_of_mem_primeFactorsList hℓL)
  have hprod : ∀ z ∈ J₀, ((L.prod : ℕ) : ℤ) • z ∈ J := by
    intro z hz
    rw [hLdef, Nat.prod_primeFactorsList hm0, natCast_zsmul]
    exact AddSubgroup.nsmul_relIndex_mem J.toAddSubgroup (K := J₀.toAddSubgroup) hz
  obtain ⟨V, hV, ψ, hψ, ψ', hψ', -, hKψ, h₁, h₂⟩ :=
    descend (X₀ := X₁) (Λ := Λ₁) (θ := θ₁) (d := d) L hL W (χ : Pt κ X₁ →+ Pt κ W) J₀ hF hJ₀mul J hJ1 hJmul hprod
  exact ⟨V, hV, ψ, hψ, ψ', hψ', hKψ, h₁, h₂⟩

end S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox
end P2MW
export P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox (solution)
