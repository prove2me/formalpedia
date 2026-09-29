-- Prove2me | solution 1 for CerednikDrinfeld.exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/01a1b88f-7f33-52e8-ad55-4e7da62a8cc4

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
import Theorems.Thm_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet
import Theorems.Thm_CerednikDrinfeld_exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_CerednikDrinfeld_exists_mem_rationalHomSet_comp_eq_id_forall_mem_ker_of_image_kernelIdealSet_eq_image_mul
import Theorems.Thm_QuaternionAlgebra_IsOrder_heckeKernel_primeHeckeSet_mk_mk_eq_natCard
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_localBox_eq_localBox_of_isMaximalOrder_of_le_of_not_dvd
import Theorems.Thm_Submodule_mem_localBox_ofFiniteIdele_iff
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld IsDedekindDomain"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange"
namespace BrandtLevel
p2m_open "CerednikDrinfeld"

section Points

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) : WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp [bc]

variable [DecidableEq k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

section Generic

variable (W : WeierstrassCurve F)

def Good (B : Set k) (P : Pt k W) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

omit [DecidableEq k] in
theorem exists_some_of_eq {Q : Pt k W} {x₁ y₁ : k} {h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁}
    (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

omit [DecidableEq k] in
theorem finite_setOf_equation (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
theorem finite_not_good {B : Set k} (hB : B.Finite) : {P : Pt k W | ¬ Good W B P}.Finite := by
  have hfin : (insert (0 : Pt k W) (⋃ x ∈ B, ⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation x y},
      {P : Pt k W | ∃ h : (W.baseChange k).toAffine.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W x) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq, Good, not_exists, not_and, not_not] at hP
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hP x y h rfl, y, h.left, h, rfl⟩

omit [DecidableEq k] in

theorem infinite_point [IsAlgClosed k] [W.IsElliptic] : Infinite (Pt k W) := by
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

end Generic

variable {W₁ W₂ : WeierstrassCurve F}

theorem finite_ker {α : Pt k W₁ →+ Pt k W₂} (hα : IsRationallyRepresented k W₁ W₂ α) :
    {P | α P = 0}.Finite := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine (finite_not_good W₁ hB).subset ?_
  rintro P (hP : α P = 0) ⟨x, y, h, rfl, hx⟩
  obtain ⟨-, -, h', hP'⟩ := hrep x y h hx
  rw [hP'] at hP
  exact absurd hP (by rintro ⟨⟩)

theorem neg_mem_rationalHomSet {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) :
    -α ∈ rationalHomSet k W₁ W₂ := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · rw [neg_zero]; exact zero_mem_rationalHomSet k W₁ W₂
  refine Or.inr ⟨nX, dX, -(nY * dX) - C (C W₂.a₁) * nX * dY - C (C W₂.a₃) * dX * dY, dY * dX,
    B, hB, ?_⟩
  intro x y h hx
  obtain ⟨hdX, hdY, h', hP⟩ := hrep x y h hx
  simp only [evalEvalBC_eq] at hdX hdY hP ⊢
  refine ⟨hdX, by rw [map_mul]; exact mul_ne_zero hdY hdX, ?_⟩
  have hneg : (-α) (.some x y h) =
      .some (bc x y nX / bc x y dX)
        ((W₂.baseChange k).toAffine.negY (bc x y nX / bc x y dX) (bc x y nY / bc x y dY))
        ((Affine.nonsingular_neg ..).mpr h') := by
    rw [AddMonoidHom.neg_apply, hP]; rfl
  refine exists_some_of_eq W₂ hneg rfl ?_
  simp only [Affine.negY, map_sub, map_neg, map_mul, bc_CC]
  change -(bc x y nY / bc x y dY) - algebraMap F k W₂.a₁ * (bc x y nX / bc x y dX)
      - algebraMap F k W₂.a₃ = _
  field_simp

theorem sub_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂)
    (hβ : β ∈ rationalHomSet k W₁ W₂) : α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet hβ)

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

theorem mem_rationalHomSet_of_mem_end [IsAlgClosed k] {W : WeierstrassCurve F} [W.IsElliptic]
    {φ : AddMonoid.End (Pt k W)} (hφ : φ ∈ rationalEndSubring k W) :
    (φ : Pt k W →+ Pt k W) ∈ rationalHomSet k W W := by
  induction hφ using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_rationalHomSet k W W
  | one => exact id_mem_rationalHomSet k W
  | add x y _ _ hx hy => exact add_mem_rationalHomSet k W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet hx
  | mul x y _ _ hx hy => exact comp_mem_rationalHomSet k W W W hy hx

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

theorem units_smul_le_iff (e : (ℍ[ℚ, a, b])ˣ) (I J : Submodule ℤ ℍ[ℚ, a, b]) :
    e • I ≤ J ↔ I ≤ e⁻¹ • J := by
  constructor
  · intro h z hz
    rw [mem_units_smul_iff, inv_inv]
    exact h ((mem_units_smul_iff e I _).mpr (by rwa [← mul_assoc, Units.inv_mul, one_mul]))
  · intro h z hz
    have := h ((mem_units_smul_iff e I z).mp hz)
    rwa [mem_units_smul_iff, inv_inv, ← mul_assoc, Units.mul_inv, one_mul] at this

end Quaternion

section Adelic

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
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
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, 1, fun v => one_mem _, rfl⟩

theorem mul_mem_ofFiniteIdele {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) {z μ : ℍ[ℚ, a, b]}
    (hz : z ∈ Submodule.ofFiniteIdele Λ g) (hμ : μ ∈ Λ) : z * μ ∈ Submodule.ofFiniteIdele Λ g := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨w * μ ⊗ₜ[ℚ] (1 : 𝔸f), mul_mem_finiteAdeleBox hΛ hw (tmul_one_mem_finiteAdeleBox hμ), ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← mul_assoc, hwz, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

variable (Λ : Submodule ℤ ℍ[ℚ, a, b])

theorem ofFiniteIdele_mul_of_mem (hΛ : IsOrder Λ)
    (x u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    Submodule.ofFiniteIdele Λ (x * u) = Submodule.ofFiniteIdele Λ x :=
  ((Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop x (x * u)).mpr
    (by rwa [inv_mul_cancel_left])).symm

theorem mk_eq_mk_of_ofFiniteIdele_eq_smul (hΛ : IsOrder Λ)
    {x x' : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ} (δ : (ℍ[ℚ, a, b])ˣ)
    (h : Submodule.ofFiniteIdele Λ x' = δ • Submodule.ofFiniteIdele Λ x) :
    ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x' = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x := by
  rw [← Submodule.ofFiniteIdele_diagonal_mul] at h
  have hu := (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop
    (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) x').mp h.symm
  have : x' = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * (x⁻¹ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ)⁻¹ * x') := by
    group
  rw [this]
  refine ((DoubleCoset.eq _ _ _ _).mpr ⟨_, MonoidHom.mem_range.mpr ⟨δ, rfl⟩, _, ?_, rfl⟩).symm
  simpa only [mul_inv_rev, mul_assoc] using hu

def place (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_place (p : ℕ) (hp : p.Prime) : Rat.HeightOneSpectrum.natGenerator (place p hp) = p := by
  have : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place p hp) = ⟨p, hp⟩ := by simp [place]
  exact congrArg Subtype.val this

theorem natCast_mem_asIdeal_place_iff (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ (place p hp).asIdeal ↔ p ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

end Adelic

section Frame

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}

def homGrp (W X₀ : WeierstrassCurve κ) [W.IsElliptic] [X₀.IsElliptic] : AddSubgroup (Pt κ W →+ Pt κ X₀) where
  carrier := rationalHomSet κ W X₀
  zero_mem' := zero_mem_rationalHomSet κ W X₀
  add_mem' ha hb := add_mem_rationalHomSet κ W X₀ ha hb
  neg_mem' ha := neg_mem_rationalHomSet ha

variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]

theorem mem_homGrp {ρ : Pt κ W →+ Pt κ X₀} : ρ ∈ homGrp W X₀ ↔ ρ ∈ rationalHomSet κ W X₀ := Iff.rfl

theorem closure_rationalHomSet : AddSubgroup.closure (rationalHomSet κ W X₀) = homGrp W X₀ :=
  le_antisymm ((AddSubgroup.closure_le _).mpr fun _ h => h) fun _ h => AddSubgroup.subset_closure h

structure IsKernelFrame (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (χ : Pt κ X₀ →+ Pt κ W) (d : (ℍ[ℚ, a, b])ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Prop where
  isOrder : IsOrder Λ
  inj : Function.Injective θ
  range_eq : Set.range θ = (Λ : Set ℍ[ℚ, a, b])
  mem : χ ∈ rationalHomSet κ X₀ W
  ne_zero : χ ≠ 0
  ker_eq : θ '' (kernelIdealSet κ X₀ W χ) =
    star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])

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
  {d : (ℍ[ℚ, a, b])ˣ} {x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

theorem IsKernelFrame.compEnd_injective (hF : IsKernelFrame Λ θ χ d x) : Function.Injective (compEnd hF.mem) := by
  intro ρ ρ' h
  have h2 := congrArg (fun e : ↥(rationalEndSubring κ X₀) => (e : AddMonoid.End (Pt κ X₀))) h
  simp only [coe_compEnd] at h2
  apply Subtype.ext
  ext Q
  obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hF.mem hF.ne_zero Q
  exact DFunLike.congr_fun h2 P

theorem IsKernelFrame.tr_injective (hF : IsKernelFrame Λ θ χ d x) : Function.Injective (tr θ hF.mem d) := by
  intro ρ ρ' h
  rw [tr_apply, tr_apply] at h
  have h1 := star_injective ((Units.mul_right_inj _).mp h)
  exact hF.compEnd_injective (hF.inj h1)

theorem IsKernelFrame.range_tr (hF : IsKernelFrame Λ θ χ d x) :
    Set.range (tr θ hF.mem d) = (Submodule.ofFiniteIdele Λ x : Set ℍ[ℚ, a, b]) := by
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

theorem IsKernelFrame.tr_mem (hF : IsKernelFrame Λ θ χ d x) (ρ : homGrp W X₀) :
    tr θ hF.mem d ρ ∈ Submodule.ofFiniteIdele Λ x := by
  rw [← SetLike.mem_coe, ← hF.range_tr]; exact ⟨ρ, rfl⟩

theorem IsKernelFrame.exists_tr_eq (hF : IsKernelFrame Λ θ χ d x) {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ x) :
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
  neg_mem' {u} hu := ⟨neg_mem_rationalHomSet hu.1, fun P hP => by
    change (-u) P = 0
    rw [AddMonoidHom.neg_apply, show u P = 0 from hu.2 hP, neg_zero]⟩

theorem mem_ann {U : AddSubgroup (Pt κ W)} {ρ : Pt κ W →+ Pt κ X₀} :
    ρ ∈ ann X₀ U ↔ ρ ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.ker := Iff.rfl

theorem ann_le_homGrp (U : AddSubgroup (Pt κ W)) : ann X₀ U ≤ homGrp W X₀ := fun _ h => h.1

theorem closure_ann (U : AddSubgroup (Pt κ W)) :
    AddSubgroup.closure {ρ | ρ ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.ker} = ann X₀ U :=
  le_antisymm ((AddSubgroup.closure_le _).mpr fun _ h => h) fun _ h => AddSubgroup.subset_closure h

def ann' (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (U : AddSubgroup (Pt κ W)) : AddSubgroup (homGrp W X₀) :=
  (ann X₀ U).addSubgroupOf (homGrp W X₀)

theorem mem_ann' {U : AddSubgroup (Pt κ W)} {ρ : homGrp W X₀} : ρ ∈ ann' X₀ U ↔ U ≤ ρ.1.ker :=
  ⟨fun h => h.2, fun h => ⟨ρ.2, h⟩⟩

def latOf (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W)
    (d : (ℍ[ℚ, a, b])ˣ) (U : AddSubgroup (Pt κ W)) : Submodule ℤ ℍ[ℚ, a, b] :=
  AddSubgroup.toIntSubmodule ((ann' X₀ U).map (tr θ hχ d))

theorem mem_latOf_iff (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (U : AddSubgroup (Pt κ W)) (z : ℍ[ℚ, a, b]) :
    z ∈ latOf θ hχ d U ↔ ∃ ρ : homGrp W X₀, U ≤ ρ.1.ker ∧ tr θ hχ d ρ = z := by
  change z ∈ (ann' X₀ U).map (tr θ hχ d) ↔ _
  rw [AddSubgroup.mem_map]
  simp only [mem_ann']

theorem toAddSubgroup_latOf (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (U : AddSubgroup (Pt κ W)) :
    (latOf θ hχ d U).toAddSubgroup = (ann' X₀ U).map (tr θ hχ d) := rfl

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

theorem addSubgroupOf_modOf (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) :
    (modOf θ hχ d J).addSubgroupOf (homGrp W X₀) = (J.toAddSubgroup).comap (tr θ hχ d) := by
  unfold modOf AddSubgroup.addSubgroupOf
  exact AddSubgroup.comap_map_eq_self_of_injective Subtype.coe_injective _

def jker (ℓ : ℕ) (M : AddSubgroup (Pt κ W →+ Pt κ X₀)) : AddSubgroup (Pt κ W) where
  carrier := {P | (ℓ : ℤ) • P = 0 ∧ ∀ μ ∈ M, μ P = 0}
  zero_mem' := ⟨smul_zero _, fun μ _ => map_zero μ⟩
  add_mem' {P Q} hP hQ := ⟨by rw [smul_add, hP.1, hQ.1, add_zero], fun μ hμ => by rw [map_add, hP.2 μ hμ, hQ.2 μ hμ, add_zero]⟩
  neg_mem' {P} hP := ⟨by rw [smul_neg, hP.1, neg_zero], fun μ hμ => by rw [map_neg, hP.2 μ hμ, neg_zero]⟩

theorem mem_jker {ℓ : ℕ} {M : AddSubgroup (Pt κ W →+ Pt κ X₀)} {P : Pt κ W} :
    P ∈ jker ℓ M ↔ (ℓ : ℤ) • P = 0 ∧ ∀ μ ∈ M, μ P = 0 := Iff.rfl

theorem IsKernelFrame.map_top_tr (hF : IsKernelFrame Λ θ χ d x) :
    (⊤ : AddSubgroup (homGrp W X₀)).map (tr θ hF.mem d) = (Submodule.ofFiniteIdele Λ x).toAddSubgroup := by
  rw [← AddMonoidHom.range_eq_map]
  ext z
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, ← SetLike.mem_coe, ← hF.range_tr, Set.mem_range]

theorem IsKernelFrame.relIndex_latOf (hF : IsKernelFrame Λ θ χ d x) (U : AddSubgroup (Pt κ W)) :
    (latOf θ hF.mem d U).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ x).toAddSubgroup =
      (ann X₀ U).relIndex (homGrp W X₀) := by
  rw [toAddSubgroup_latOf, ← hF.map_top_tr, ← AddSubgroup.relIndex_comap,
    AddSubgroup.comap_map_eq_self_of_injective hF.tr_injective, AddSubgroup.relIndex_top_right]
  rfl

theorem IsKernelFrame.relIndex_modOf (hF : IsKernelFrame Λ θ χ d x) (J : Submodule ℤ ℍ[ℚ, a, b]) :
    (modOf θ hF.mem d J).relIndex (homGrp W X₀) =
      J.toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ x).toAddSubgroup := by
  rw [AddSubgroup.relIndex, addSubgroupOf_modOf, ← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap,
    hF.map_top_tr]

theorem IsKernelFrame.exists_ne_zero (hF : IsKernelFrame Λ θ χ d x) : ∃ σ ∈ rationalHomSet κ W X₀, σ ≠ 0 := by
  obtain ⟨σ, hσ, n, hn, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₀ W hF.mem hF.ne_zero
  refine ⟨σ, hσ, fun h0 => smul_id_ne_zero (k := κ) X₀ hn.ne' ?_⟩
  ext P
  rw [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, ← hdual.comp_left P, h0,
    AddMonoidHom.zero_apply]

theorem IsKernelFrame.dictA (hF : IsKernelFrame Λ θ χ d x) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    (U : AddSubgroup (Pt κ W)) (hUℓ : ∀ P ∈ U, (ℓ : ℤ) • P = 0) :
    {P : Pt κ W | (ℓ : ℤ) • P = 0 ∧ ∀ ρ ∈ rationalHomSet κ W X₀, U ≤ ρ.ker → ρ P = 0} = (U : Set _) ∧
      (ann X₀ U).relIndex (homGrp W X₀) = Nat.card U ^ 2 := by
  obtain ⟨h1, h2⟩ := (WeierstrassCurve.relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero X₀ a b Λ
    hF.isOrder θ hF.inj hF.range_eq W hF.exists_ne_zero ℓ hℓ hℓκ).1 U hUℓ
  rw [closure_ann, closure_rationalHomSet] at h2
  exact ⟨h1, h2⟩

theorem IsKernelFrame.dictB (hF : IsKernelFrame Λ θ χ d x) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    (M : AddSubgroup (Pt κ W →+ Pt κ X₀)) (hMH : (M : Set _) ⊆ rationalHomSet κ W X₀)
    (hMℓ : ∀ ρ ∈ rationalHomSet κ W X₀, ℓ • ρ ∈ M)
    (hMR : ∀ α ∈ rationalHomSet κ X₀ X₀, ∀ ρ ∈ M, α.comp ρ ∈ M)
    (ρ : Pt κ W →+ Pt κ X₀) (hρ : ρ ∈ rationalHomSet κ W X₀)
    (hρK : ∀ P : Pt κ W, (ℓ : ℤ) • P = 0 → (∀ μ ∈ M, μ P = 0) → ρ P = 0) : ρ ∈ M :=
  (WeierstrassCurve.relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero X₀ a b Λ
    hF.isOrder θ hF.inj hF.range_eq W hF.exists_ne_zero ℓ hℓ hℓκ).2 M hMH hMℓ hMR ρ hρ hρK

omit [IsAlgClosed κ] [DecidableEq κ] in

theorem isEichlerOrder_one {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) : IsEichlerOrder Λ 1 :=
  ⟨Λ, Λ, hΛ, hΛ, (inf_idem _).symm, AddSubgroup.relIndex_self _⟩

omit [IsAlgClosed κ] [DecidableEq κ] in

theorem heckeLattice_iff (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) :
    (∃ h ∈ primeHeckeSet Λ ℓ, J = Submodule.ofFiniteIdele Λ (g * h)) ↔
      (J ≤ Submodule.ofFiniteIdele Λ g ∧
        (∀ z ∈ Submodule.ofFiniteIdele Λ g, (ℓ : ℚ) • z ∈ J) ∧
        (∃ y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, J = Submodule.ofFiniteIdele Λ y) ∧
        J.toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ g).toAddSubgroup = ℓ ^ 2) := by
  set v := place ℓ hℓ with hv
  have hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal := (natCast_mem_asIdeal_place_iff ℓ hℓ ℓ).mpr dvd_rfl
  have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have hd := (natCast_mem_asIdeal_place_iff ℓ hℓ q').mp h
    exact hℓq ((Nat.prime_dvd_prime_iff_eq hℓ (Fact.out : q'.Prime)).mp hd)
  have h1v : ((1 : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp ((natCast_mem_asIdeal_place_iff ℓ hℓ 1).mp h))
  obtain ⟨φ, hφ, hRv⟩ := QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef
    (isEichlerOrder_one hΛ) v hq'v h1v
  exact QuaternionAlgebra.IsOrder.exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff hΛ.isOrder hℓ v hℓv φ hφ hRv g J

omit [IsAlgClosed κ] [DecidableEq κ] in
theorem cast_ne_zero_of_ne (q' : ℕ) [Fact q'.Prime] [CharP κ q'] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q') :
    (ℓ : κ) ≠ 0 := by
  intro h
  have hd : q' ∣ ℓ := (CharP.cast_eq_zero_iff κ q' ℓ).mp h
  exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hℓ).mp hd).symm

theorem nsmul_eq_zero_of_mem_of_card {U : AddSubgroup (Pt κ W)} {ℓ : ℕ} (hU : Nat.card U = ℓ) {P : Pt κ W} (hP : P ∈ U) :
    (ℓ : ℤ) • P = 0 := by
  have h := card_nsmul_eq_zero' (x := (⟨P, hP⟩ : U))
  rw [hU] at h
  rw [natCast_zsmul]
  exact congrArg Subtype.val h

end Frame

section VarChange

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate

variable {k : Type*} [Field k] [DecidableEq k]

omit [DecidableEq k] in
private theorem exists_eq_some {W : WeierstrassCurve k}
    {P : W.toAffine.Point} {u v u' v' : k}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀)
    (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

theorem addEquiv_mem_rationalHomSet (W : WeierstrassCurve k) (γ : VariableChange k)
    (e : W.toAffine.Point ≃+ (γ • W).toAffine.Point)
    (he : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      ∃ h' : (γ • W).toAffine.Nonsingular ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
        ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))),
        e (.some x y h) = .some ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
          ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))) h') :
    (e.toAddMonoidHom : (W.baseChange k).toAffine.Point →+ ((γ • W).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (γ • W) := by
  right
  refine ⟨C (C ((↑γ.u⁻¹ : k) ^ 2) * (X - C γ.r)), 1,
    C (C ((↑γ.u⁻¹ : k) ^ 3)) * (X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))), 1, ∅,
    Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC (F := k) k (1 : k[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := k) k (C (C ((↑γ.u⁻¹ : k) ^ 2) * (X - C γ.r)) : k[X][Y]) x y =
      (↑γ.u⁻¹ : k) ^ 2 * (x - γ.r) := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := k) k
      (C (C ((↑γ.u⁻¹ : k) ^ 3)) * (X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))) : k[X][Y]) x y =
      (↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t)) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  obtain ⟨h', hP⟩ := he x y h
  exact exists_eq_some hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])

theorem addEquiv_symm_mem_rationalHomSet (W : WeierstrassCurve k) (γ : VariableChange k)
    (e : W.toAffine.Point ≃+ (γ • W).toAffine.Point)
    (he : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      ∃ h' : (γ • W).toAffine.Nonsingular ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
        ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))),
        e (.some x y h) = .some ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
          ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))) h') :
    (e.symm.toAddMonoidHom :
        ((γ • W).baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k (γ • W) W := by
  right
  refine ⟨C (C ((γ.u : k) ^ 2) * X + C γ.r), 1,
    C (C ((γ.u : k) ^ 3)) * X + C (C ((γ.u : k) ^ 2 * γ.s) * X + C γ.t), 1, ∅,
    Set.finite_empty, fun x' y' h' _ => ?_⟩
  have e0 : evalEvalBC (F := k) k (1 : k[X][Y]) x' y' = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := k) k (C (C ((γ.u : k) ^ 2) * X + C γ.r) : k[X][Y]) x' y' =
      (γ.u : k) ^ 2 * x' + γ.r := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := k) k
      (C (C ((γ.u : k) ^ 3)) * X + C (C ((γ.u : k) ^ 2 * γ.s) * X + C γ.t) : k[X][Y]) x' y' =
      (γ.u : k) ^ 3 * y' + ((γ.u : k) ^ 2 * γ.s * x' + γ.t) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  set P := e.symm (.some x' y' h') with hPdef
  have hP0 : P ≠ 0 := by
    intro h0
    have : e P = e 0 := by rw [h0]
    rw [hPdef, AddEquiv.apply_symm_apply, _root_.map_zero] at this
    exact Affine.Point.some_ne_zero _ this
  rcases hPxy : P with _ | ⟨x, y, h⟩
  · exact absurd hPxy hP0
  · obtain ⟨h'', hexy⟩ := he x y h
    have key : e (.some x y h) = .some x' y' h' := by
      rw [← hPxy, hPdef, AddEquiv.apply_symm_apply]
    rw [hexy] at key
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj key
    have hw : (↑γ.u⁻¹ : k) = (γ.u : k)⁻¹ := Units.val_inv_eq_inv_val γ.u
    have hu0 : (γ.u : k) ≠ 0 := γ.u.ne_zero
    have hPe : e.symm.toAddMonoidHom (.some x' y' h') = .some x y h := by
      show e.symm (.some x' y' h') = .some x y h
      rw [← hPdef]; exact hPxy
    refine exists_eq_some hPe ?_ ?_
    · rw [e0, e1, div_one, ← hx, hw]
      field_simp
      ring
    · rw [e0, e2, div_one, ← hx, ← hy, hw]
      field_simp
      ring

end VarChange

section SubgroupToLattice

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₀ W W' : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic] [W'.IsElliptic]

theorem nsmul_id_ne_zero (W : WeierstrassCurve κ) [W.IsElliptic] {ℓ : ℕ} (hℓ : ℓ ≠ 0) (hℓκ : (ℓ : κ) ≠ 0) :
    (ℓ • AddMonoidHom.id (Pt κ W)) ≠ 0 := by
  intro h
  have h0 := eq_zero_of_nsmul_eq_zero (id_mem_rationalHomSet κ W) hℓ hℓκ h
  haveI := infinite_point (k := κ) W
  obtain ⟨P, hP⟩ := exists_ne (0 : Pt κ W)
  exact hP (by simpa using DFunLike.congr_fun h0 P)

theorem mem_ann_iff_of_dualPair {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    {U : AddSubgroup (Pt κ W)} (hU : Nat.card U = ℓ)
    {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') {ψ' : Pt κ W' →+ Pt κ W}
    (hψ' : ψ' ∈ rationalHomSet κ W' W) (hker : ψ.ker = U)
    (h1 : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (h2 : ψ.comp ψ' = ℓ • AddMonoidHom.id _)
    (ρ : Pt κ W →+ Pt κ X₀) :
    ρ ∈ ann X₀ U ↔ ∃ ρ' ∈ rationalHomSet κ W' X₀, ρ = ρ'.comp ψ := by
  constructor
  · rintro ⟨hρ, hρU⟩

    have hUκ : ((Nat.card U : ℕ) : κ) ≠ 0 := by rw [hU]; exact hℓκ
    obtain ⟨V, hV, π, hπ, hπs, hπker, huniv⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp W U hUκ
    haveI := hV
    obtain ⟨ρV, hρV, hρeq⟩ := huniv X₀ ρ hρ hρU

    have hψ0 : ψ ≠ 0 := by
      intro h0
      apply nsmul_id_ne_zero W hℓ.ne_zero hℓκ
      rw [← h1, h0, AddMonoidHom.comp_zero]
    have hψs := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hψ hψ0

    have hkill : ∀ Q : Pt κ W', (ℓ : ℤ) • Q = 0 → (π.comp ψ') Q = 0 := by
      intro Q hQ
      obtain ⟨P, rfl⟩ := hψs Q
      have hℓP : ℓ • P ∈ U := by
        rw [← hker, AddMonoidHom.mem_ker, map_nsmul, ← natCast_zsmul, hQ]
      rw [AddMonoidHom.comp_apply, show ψ' (ψ P) = (ψ'.comp ψ) P from rfl, h1, AddMonoidHom.nsmul_apply,
        AddMonoidHom.id_apply]
      rw [← hπker] at hℓP
      exact hℓP
    obtain ⟨β, hβ, hβeq⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W' V hℓκ
      (comp_mem_rationalHomSet κ W' W V hψ' hπ) hkill

    have hβψ : β.comp ψ = π := by
      have hD : β.comp ψ - π ∈ rationalHomSet κ W V :=
        sub_mem_rationalHomSet (comp_mem_rationalHomSet κ W W' V hψ hβ) hπ
      have hℓD : ℓ • (β.comp ψ - π) = 0 := by
        ext P
        rw [AddMonoidHom.nsmul_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, smul_sub,
          ← natCast_zsmul, ← hβeq (ψ P), AddMonoidHom.comp_apply, show ψ' (ψ P) = (ψ'.comp ψ) P from rfl, h1,
          AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, map_nsmul, AddMonoidHom.zero_apply, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_nsmul_eq_zero hD hℓ.ne_zero hℓκ hℓD)
    refine ⟨ρV.comp β, comp_mem_rationalHomSet κ W' V X₀ hβ hρV, ?_⟩
    rw [AddMonoidHom.comp_assoc, hβψ]; exact hρeq
  · rintro ⟨ρ', hρ', rfl⟩
    refine ⟨comp_mem_rationalHomSet κ W W' X₀ hψ hρ', fun P hP => ?_⟩
    rw [← hker] at hP
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, show ψ P = 0 from hP, map_zero]

theorem mem_ann_iff_of_dualPair' {ℓ : ℕ} (hℓ : ℓ ≠ 0) (hℓκ : (ℓ : κ) ≠ 0)
    {U : AddSubgroup (Pt κ W)} (hU : Nat.card U = ℓ)
    {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') {ψ' : Pt κ W' →+ Pt κ W}
    (hψ' : ψ' ∈ rationalHomSet κ W' W) (hker : ψ.ker = U)
    (h1 : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (h2 : ψ.comp ψ' = ℓ • AddMonoidHom.id _)
    (ρ : Pt κ W →+ Pt κ X₀) :
    ρ ∈ ann X₀ U ↔ ∃ ρ' ∈ rationalHomSet κ W' X₀, ρ = ρ'.comp ψ := by
  constructor
  · rintro ⟨hρ, hρU⟩

    have hUκ : ((Nat.card U : ℕ) : κ) ≠ 0 := by rw [hU]; exact hℓκ
    obtain ⟨V, hV, π, hπ, hπs, hπker, huniv⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp W U hUκ
    haveI := hV
    obtain ⟨ρV, hρV, hρeq⟩ := huniv X₀ ρ hρ hρU

    have hψ0 : ψ ≠ 0 := by
      intro h0
      apply nsmul_id_ne_zero W hℓ hℓκ
      rw [← h1, h0, AddMonoidHom.comp_zero]
    have hψs := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hψ hψ0

    have hkill : ∀ Q : Pt κ W', (ℓ : ℤ) • Q = 0 → (π.comp ψ') Q = 0 := by
      intro Q hQ
      obtain ⟨P, rfl⟩ := hψs Q
      have hℓP : ℓ • P ∈ U := by
        rw [← hker, AddMonoidHom.mem_ker, map_nsmul, ← natCast_zsmul, hQ]
      rw [AddMonoidHom.comp_apply, show ψ' (ψ P) = (ψ'.comp ψ) P from rfl, h1, AddMonoidHom.nsmul_apply,
        AddMonoidHom.id_apply]
      rw [← hπker] at hℓP
      exact hℓP
    obtain ⟨β, hβ, hβeq⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W' V hℓκ
      (comp_mem_rationalHomSet κ W' W V hψ' hπ) hkill

    have hβψ : β.comp ψ = π := by
      have hD : β.comp ψ - π ∈ rationalHomSet κ W V :=
        sub_mem_rationalHomSet (comp_mem_rationalHomSet κ W W' V hψ hβ) hπ
      have hℓD : ℓ • (β.comp ψ - π) = 0 := by
        ext P
        rw [AddMonoidHom.nsmul_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, smul_sub,
          ← natCast_zsmul, ← hβeq (ψ P), AddMonoidHom.comp_apply, show ψ' (ψ P) = (ψ'.comp ψ) P from rfl, h1,
          AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, map_nsmul, AddMonoidHom.zero_apply, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_nsmul_eq_zero hD hℓ hℓκ hℓD)
    refine ⟨ρV.comp β, comp_mem_rationalHomSet κ W' V X₀ hβ hρV, ?_⟩
    rw [AddMonoidHom.comp_assoc, hβψ]; exact hρeq
  · rintro ⟨ρ', hρ', rfl⟩
    refine ⟨comp_mem_rationalHomSet κ W W' X₀ hψ hρ', fun P hP => ?_⟩
    rw [← hker] at hP
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, show ψ P = 0 from hP, map_zero]

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]}
  {χ : Pt κ X₀ →+ Pt κ W} {d : (ℍ[ℚ, a, b])ˣ} {x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
  {χ' : Pt κ X₀ →+ Pt κ W'} {d' : (ℍ[ℚ, a, b])ˣ} {y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

theorem image_theta_ann_eq_of_dualPair (hF : IsKernelFrame Λ θ χ d x) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    {U : AddSubgroup (Pt κ W)} (hU : Nat.card U = ℓ)
    {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') {ψ' : Pt κ W' →+ Pt κ W}
    (hψ' : ψ' ∈ rationalHomSet κ W' W) (hker : ψ.ker = U)
    (h1 : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (h2 : ψ.comp ψ' = ℓ • AddMonoidHom.id _) :
    (fun ρ : homGrp W X₀ => θ (compEnd hF.mem ρ)) '' (ann' X₀ U : Set (homGrp W X₀)) =
      θ '' (kernelIdealSet κ X₀ W' (ψ.comp χ)) := by
  ext w
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨ρ', hρ', hρeq⟩ := (mem_ann_iff_of_dualPair hℓ hℓκ hU hψ hψ' hker h1 h2 ρ.1).mp ⟨ρ.2, hρ.2⟩
    refine ⟨compEnd hF.mem ρ, ⟨ρ', hρ', ?_⟩, rfl⟩
    rw [coe_compEnd, hρeq]; rfl
  · rintro ⟨e, ⟨ρ', hρ', he⟩, rfl⟩
    have hmem : ρ'.comp ψ ∈ ann X₀ U := (mem_ann_iff_of_dualPair hℓ hℓκ hU hψ hψ' hker h1 h2 _).mpr ⟨ρ', hρ', rfl⟩
    refine ⟨⟨ρ'.comp ψ, hmem.1⟩, hmem, ?_⟩
    congr 1
    exact Subtype.ext (by rw [coe_compEnd, he]; rfl)

theorem image_theta_ann_eq_of_dualPair' (hF : IsKernelFrame Λ θ χ d x) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (hℓκ : (ℓ : κ) ≠ 0)
    {U : AddSubgroup (Pt κ W)} (hU : Nat.card U = ℓ)
    {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') {ψ' : Pt κ W' →+ Pt κ W}
    (hψ' : ψ' ∈ rationalHomSet κ W' W) (hker : ψ.ker = U)
    (h1 : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (h2 : ψ.comp ψ' = ℓ • AddMonoidHom.id _) :
    (fun ρ : homGrp W X₀ => θ (compEnd hF.mem ρ)) '' (ann' X₀ U : Set (homGrp W X₀)) =
      θ '' (kernelIdealSet κ X₀ W' (ψ.comp χ)) := by
  ext w
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨ρ', hρ', hρeq⟩ := (mem_ann_iff_of_dualPair' hℓ hℓκ hU hψ hψ' hker h1 h2 ρ.1).mp ⟨ρ.2, hρ.2⟩
    refine ⟨compEnd hF.mem ρ, ⟨ρ', hρ', ?_⟩, rfl⟩
    rw [coe_compEnd, hρeq]; rfl
  · rintro ⟨e, ⟨ρ', hρ', he⟩, rfl⟩
    have hmem : ρ'.comp ψ ∈ ann X₀ U := (mem_ann_iff_of_dualPair' hℓ hℓκ hU hψ hψ' hker h1 h2 _).mpr ⟨ρ', hρ', rfl⟩
    refine ⟨⟨ρ'.comp ψ, hmem.1⟩, hmem, ?_⟩
    congr 1
    exact Subtype.ext (by rw [coe_compEnd, he]; rfl)

theorem exists_latOf_eq_smul_of_dualPair (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (hss : ∀ P : Pt κ X₀, q' • P = 0 → P = 0) (ha : a < 0) (hb : b < 0)
    (hF : IsKernelFrame Λ θ χ d x) (hF' : IsKernelFrame Λ θ χ' d' y)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    {U : AddSubgroup (Pt κ W)} (hU : Nat.card U = ℓ)
    {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') {ψ' : Pt κ W' →+ Pt κ W}
    (hψ' : ψ' ∈ rationalHomSet κ W' W) (hker : ψ.ker = U)
    (h1 : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (h2 : ψ.comp ψ' = ℓ • AddMonoidHom.id _) :
    ∃ e : (ℍ[ℚ, a, b])ˣ, latOf θ hF.mem d U = e • Submodule.ofFiniteIdele Λ y := by

  have hψ0 : ψ ≠ 0 := by
    intro h0
    apply nsmul_id_ne_zero W hℓ.ne_zero hℓκ
    rw [← h1, h0, AddMonoidHom.comp_zero]
  have hψχ : ψ.comp χ ∈ rationalHomSet κ X₀ W' := comp_mem_rationalHomSet κ X₀ W W' hF.mem hψ
  have hψχ0 : ψ.comp χ ≠ 0 := by
    intro h0
    have hs := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hF.mem hF.ne_zero
    apply hψ0
    ext Q
    obtain ⟨P, rfl⟩ := hs Q
    exact DFunLike.congr_fun h0 P

  obtain ⟨c, hc⟩ := CerednikDrinfeld.exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange q' X₀ hss a b
    ha hb θ hF.inj W' W' (ψ.comp χ) hψχ hψχ0 χ' hF'.mem hF'.ne_zero ⟨1, one_smul _ _⟩

  have hiff : ∀ w : ℍ[ℚ, a, b], w ∈ θ '' (kernelIdealSet κ X₀ W' (ψ.comp χ)) ↔
      w * c ∈ star '' ((d' • Submodule.ofFiniteIdele Λ y : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
    intro w
    rw [← hF'.ker_eq, hc]
    constructor
    · intro hw; exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      have : w' = w := (Units.mul_left_inj c).mp hww'
      rwa [this] at hw'
  refine ⟨d⁻¹ * (star c)⁻¹ * d', ?_⟩
  ext z
  rw [mem_latOf_iff, mem_units_smul_iff]
  have hkey : (∃ ρ : homGrp W X₀, U ≤ ρ.1.ker ∧ tr θ hF.mem d ρ = z) ↔
      star ((d : ℍ[ℚ, a, b]) * z) ∈ θ '' (kernelIdealSet κ X₀ W' (ψ.comp χ)) := by
    rw [← image_theta_ann_eq_of_dualPair hF hℓ hℓκ hU hψ hψ' hker h1 h2]
    simp only [Set.mem_image, SetLike.mem_coe, mem_ann']
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ, hρ, by rw [theta_compEnd_eq θ hF.mem d ρ]⟩
    · rintro ⟨ρ, hρ, hρz⟩
      refine ⟨ρ, hρ, ?_⟩
      rw [theta_compEnd_eq θ hF.mem d ρ] at hρz
      exact (Units.mul_right_inj d).mp (star_injective hρz)
  rw [hkey, hiff]

  constructor
  · rintro ⟨w, hw, hw'⟩
    rw [SetLike.mem_coe, mem_units_smul_iff] at hw
    have h3 : star w = star ((d : ℍ[ℚ, a, b]) * z) * c := hw'
    have h4 : w = star (c : ℍ[ℚ, a, b]) * ((d : ℍ[ℚ, a, b]) * z) := by
      rw [← star_star w, h3, star_mul, star_star]
    have hz : z = ((d⁻¹ * (star c)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * w := by
      rw [h4, ← Units.coe_star, Units.val_mul]
      simp only [← mul_assoc]
      rw [Units.inv_mul_cancel_right, Units.inv_mul, one_mul]
    rw [hz, ← mul_assoc, ← Units.val_mul]
    have hu : (d⁻¹ * (star c)⁻¹ * d')⁻¹ * (d⁻¹ * (star c)⁻¹) = d'⁻¹ := by group
    rw [hu]; exact hw
  · intro hz
    refine ⟨((star c * d : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_units_smul_iff, ← mul_assoc, ← Units.val_mul]
      have hu : d'⁻¹ * (star c * d) = (d⁻¹ * (star c)⁻¹ * d')⁻¹ := by group
      rw [hu]; exact hz
    · simp only [Units.val_mul, Units.coe_star, star_mul, star_star, mul_assoc]

theorem exists_mem_primeHeckeSet_latOf_eq (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (hss : ∀ P : Pt κ X₀, q' • P = 0 → P = 0) (hdef : IsDefiniteRamifiedExactlyAt a b q') (hΛ : IsMaximalOrder Λ)
    (hF : IsKernelFrame Λ θ χ d x) (hF' : IsKernelFrame Λ θ χ' d' y)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
    {U : AddSubgroup (Pt κ W)} (hU : Nat.card U = ℓ)
    {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') {ψ' : Pt κ W' →+ Pt κ W}
    (hψ' : ψ' ∈ rationalHomSet κ W' W) (hker : ψ.ker = U)
    (h1 : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (h2 : ψ.comp ψ' = ℓ • AddMonoidHom.id _) :
    ∃ h ∈ primeHeckeSet Λ ℓ, latOf θ hF.mem d U = Submodule.ofFiniteIdele Λ (x * h) := by
  have hℓκ : (ℓ : κ) ≠ 0 := cast_ne_zero_of_ne q' hℓ hℓq
  have hUℓ : ∀ P ∈ U, (ℓ : ℤ) • P = 0 := fun P hP => nsmul_eq_zero_of_mem_of_card hU hP
  rw [heckeLattice_iff q' hdef hΛ hℓ hℓq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨ρ, -, rfl⟩ := (mem_latOf_iff θ hF.mem d U z).mp hz
    exact hF.tr_mem ρ
  · intro z hz
    obtain ⟨ρ, rfl⟩ := hF.exists_tr_eq hz
    rw [Nat.cast_smul_eq_nsmul ℚ, ← map_nsmul]
    refine (mem_latOf_iff θ hF.mem d U _).mpr ⟨ℓ • ρ, ?_, rfl⟩
    intro P hP
    rw [AddMonoidHom.mem_ker]
    change (ℓ • ρ.1) P = 0
    rw [AddMonoidHom.nsmul_apply, ← natCast_zsmul, ← map_zsmul, hUℓ P hP, map_zero]
  · obtain ⟨e, he⟩ := exists_latOf_eq_smul_of_dualPair q' hss hdef.neg_left hdef.neg_right hF hF' hℓ hℓκ hU hψ hψ' hker h1 h2
    exact ⟨Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] e * y, by rw [Submodule.ofFiniteIdele_diagonal_mul, he]⟩
  · rw [hF.relIndex_latOf, (hF.dictA hℓ hℓκ U hUℓ).2, hU]

end SubgroupToLattice

section Definite

variable {a b : ℚ}

theorem nrd_pos_of_ne_zero' (ha : a < 0) (hb : b < 0) {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : 0 < nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [nrd_mk]
  have h1 : 0 ≤ x₀ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ -a * x₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ -b * x₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 ≤ a * b * x₃ ^ 2 := mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg ha hb)) (sq_nonneg _)
  by_contra hle
  push Not at hle
  have e1 : x₀ ^ 2 = 0 := by nlinarith
  have e2 : -a * x₁ ^ 2 = 0 := by nlinarith
  have e3 : -b * x₂ ^ 2 = 0 := by nlinarith
  have e4 : a * b * x₃ ^ 2 = 0 := by nlinarith
  have hx₀ : x₀ = 0 := by simpa using e1
  have hx₁ : x₁ = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · linarith
    · simpa using h
  have hx₂ : x₂ = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · linarith
    · simpa using h
  have hx₃ : x₃ = 0 := by
    rcases mul_eq_zero.mp e4 with h | h
    · exact absurd h (mul_pos_of_neg_of_neg ha hb).ne'
    · simpa using h
  exact hx (by subst hx₀ hx₁ hx₂ hx₃; rfl)

theorem isUnit_of_ne_zero' (ha : a < 0) (hb : b < 0) {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : IsUnit x := by
  have hn : nrd x ≠ 0 := (nrd_pos_of_ne_zero' ha hb hx).ne'
  refine ⟨⟨x, (nrd x)⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, mul_star_eq_coe_nrd, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hn,
      QuaternionAlgebra.coe_one]
  · rw [smul_mul_assoc, star_mul_eq_coe_nrd, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hn,
      QuaternionAlgebra.coe_one]

end Definite

section Backward

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₀ W W' W₁ W₁' : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic] [W'.IsElliptic]
  [W₁.IsElliptic] [W₁'.IsElliptic]

theorem exists_units_image_pair_of_iso
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (hss : ∀ P : Pt κ X₀, q' • P = 0 → P = 0)
    (ha : a < 0) (hb : b < 0)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    {χ' : Pt κ X₀ →+ Pt κ W'} (hχ' : χ' ∈ rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0)
    {N : ℕ} (hN0 : N ≠ 0) (hNκ : (N : κ) ≠ 0)
    {ψ : Pt κ W →+ Pt κ W₁} (hψ : ψ ∈ rationalHomSet κ W W₁)
    {ψd : Pt κ W₁ →+ Pt κ W} (hψd : ψd ∈ rationalHomSet κ W₁ W)
    (hψ1 : ψd.comp ψ = N • AddMonoidHom.id _) (hψ2 : ψ.comp ψd = N • AddMonoidHom.id _)
    (hψN : Nat.card ψ.ker = N)
    {ψ' : Pt κ W' →+ Pt κ W₁'} (hψ' : ψ' ∈ rationalHomSet κ W' W₁')
    {ψd' : Pt κ W₁' →+ Pt κ W'} (hψd' : ψd' ∈ rationalHomSet κ W₁' W')
    (hψ'1 : ψd'.comp ψ' = N • AddMonoidHom.id _) (hψ'2 : ψ'.comp ψd' = N • AddMonoidHom.id _)
    (hψ'N : Nat.card ψ'.ker = N)
    {φ : Pt κ W →+ Pt κ W'} (hφ : φ ∈ rationalHomSet κ W W')
    {φ' : Pt κ W' →+ Pt κ W} (hφ' : φ' ∈ rationalHomSet κ W' W)
    (hi1 : φ'.comp φ = AddMonoidHom.id _) (hi2 : φ.comp φ' = AddMonoidHom.id _)
    (hlev : ∀ T ∈ ψ.ker, φ T ∈ ψ'.ker) :
    ∃ c : (ℍ[ℚ, a, b])ˣ,
      θ '' kernelIdealSet κ X₀ W' χ' = (· * (c : ℍ[ℚ, a, b])) '' (θ '' kernelIdealSet κ X₀ W χ) ∧
      θ '' kernelIdealSet κ X₀ W₁' (ψ'.comp χ') = (· * (c : ℍ[ℚ, a, b])) '' (θ '' kernelIdealSet κ X₀ W₁ (ψ.comp χ)) := by
  classical

  haveI : Finite ψ'.ker := Nat.finite_of_card_ne_zero (by rw [hψ'N]; exact hN0)
  haveI : Finite ψ.ker := Nat.finite_of_card_ne_zero (by rw [hψN]; exact hN0)
  have hφinj : Function.Injective φ := by
    intro P Q h
    have := congrArg φ' h
    have hP : φ' (φ P) = P := congrArg (fun f => f P) hi1
    have hQ : φ' (φ Q) = Q := congrArg (fun f => f Q) hi1
    rw [hP, hQ] at this
    exact this
  let f : ψ.ker → ψ'.ker := fun T => ⟨φ T.1, hlev T.1 T.2⟩
  have hf : Function.Injective f := by
    intro T T' h
    apply Subtype.ext
    exact hφinj (congrArg Subtype.val h)
  have hfb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hψN, hψ'N])
  have hlev' : ∀ T' ∈ ψ'.ker, φ' T' ∈ ψ.ker := by
    intro T' hT'
    obtain ⟨T, hT⟩ := hfb.2 ⟨T', hT'⟩
    have : φ T.1 = T' := congrArg Subtype.val hT
    rw [← this, show φ' (φ T.1) = T.1 from congrArg (fun f => f T.1) hi1]
    exact T.2

  set χ₂ : Pt κ X₀ →+ Pt κ W' := φ.comp χ with hχ₂def
  have hχ₂ : χ₂ ∈ rationalHomSet κ X₀ W' := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W W' hχ hφ
  have hχsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0
  have hχ₂0 : χ₂ ≠ 0 := by
    intro h0
    apply hχ0
    ext P
    have hP : φ (χ P) = 0 := congrArg (fun f => f P) h0
    have := congrArg φ' hP
    rw [show φ' (φ (χ P)) = χ P from congrArg (fun f => f (χ P)) hi1, map_zero] at this
    rw [AddMonoidHom.zero_apply]; exact this
  obtain ⟨σ₂, hσ₂, n, hn, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₀ W' hχ₂ hχ₂0
  have hs : σ₂.comp χ' ∈ rationalHomSet κ X₀ X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W' X₀ hχ' hσ₂
  set s : ↥(rationalEndSubring κ X₀) := ⟨σ₂.comp χ', Subring.subset_closure hs⟩ with hsdef

  have hF1 : ∀ ρ' ∈ rationalHomSet κ W₁' X₀, ∃ ρ ∈ rationalHomSet κ W₁ X₀, (ρ'.comp ψ').comp φ = ρ.comp ψ := by
    intro ρ' hρ'
    have hmem : (ρ'.comp ψ').comp φ ∈ ann X₀ ψ.ker := by
      refine ⟨WeierstrassCurve.comp_mem_rationalHomSet κ W W' X₀ hφ
        (WeierstrassCurve.comp_mem_rationalHomSet κ W' W₁' X₀ hψ' hρ'), fun T hT => ?_⟩
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        show ψ' (φ T) = 0 from hlev T hT, map_zero]
    obtain ⟨ρ, hρ, hρeq⟩ := (mem_ann_iff_of_dualPair' hN0 hNκ hψN hψ hψd rfl hψ1 hψ2 _).mp hmem
    exact ⟨ρ, hρ, hρeq⟩
  have hF2 : ∀ ρ ∈ rationalHomSet κ W₁ X₀, ∃ ρ' ∈ rationalHomSet κ W₁' X₀, (ρ.comp ψ).comp φ' = ρ'.comp ψ' := by
    intro ρ hρ
    have hmem : (ρ.comp ψ).comp φ' ∈ ann X₀ ψ'.ker := by
      refine ⟨WeierstrassCurve.comp_mem_rationalHomSet κ W' W X₀ hφ'
        (WeierstrassCurve.comp_mem_rationalHomSet κ W W₁ X₀ hψ hρ), fun T hT => ?_⟩
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        show ψ (φ' T) = 0 from hlev' T hT, map_zero]
    obtain ⟨ρ', hρ', hρeq⟩ := (mem_ann_iff_of_dualPair' hN0 hNκ hψ'N hψ' hψd' rfl hψ'1 hψ'2 _).mp hmem
    exact ⟨ρ', hρ', hρeq⟩

  have hA : ∀ a' ∈ kernelIdealSet κ X₀ W' χ', ∃ b' ∈ kernelIdealSet κ X₀ W χ,
      a' * (n : ↥(rationalEndSubring κ X₀)) = b' * s := by
    rintro a' ⟨ρ, hρ, hρa⟩
    have hρe : ρ.comp φ ∈ rationalHomSet κ W X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ W W' X₀ hφ hρ
    have hb : (ρ.comp φ).comp χ ∈ rationalHomSet κ X₀ X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W X₀ hχ hρe
    refine ⟨⟨_, Subring.subset_closure hb⟩, ⟨_, hρe, rfl⟩, ?_⟩
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    show (a' : AddMonoid.End (Pt κ X₀)) (((n : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt κ X₀)) P) =
      ρ (φ (χ (σ₂ (χ' P))))
    rw [SubringClass.coe_intCast, AddMonoid.End.intCast_apply, hρa]
    show ρ (χ' (n • P)) = ρ (φ (χ (σ₂ (χ' P))))
    rw [map_zsmul, ← hdual.comp_right (χ' P)]
    rfl
  have hB : ∀ b' ∈ kernelIdealSet κ X₀ W χ, ∃ a' ∈ kernelIdealSet κ X₀ W' χ',
      b' * s = a' * (n : ↥(rationalEndSubring κ X₀)) := by
    rintro b' ⟨ρ', hρ', hρb⟩
    have hρ : ρ'.comp φ' ∈ rationalHomSet κ W' X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ W' W X₀ hφ' hρ'
    have ha' : (ρ'.comp φ').comp χ' ∈ rationalHomSet κ X₀ X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W' X₀ hχ' hρ
    refine ⟨⟨_, Subring.subset_closure ha'⟩, ⟨_, hρ, rfl⟩, ?_⟩
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    show (b' : AddMonoid.End (Pt κ X₀)) (σ₂ (χ' P)) =
      ρ' (φ' (χ' (((n : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt κ X₀)) P)))
    rw [SubringClass.coe_intCast, AddMonoid.End.intCast_apply, hρb]
    show ρ' (χ (σ₂ (χ' P))) = ρ' (φ' (χ' (n • P)))
    rw [map_zsmul, ← hdual.comp_right (χ' P)]
    show ρ' (χ (σ₂ (χ' P))) = ρ' (φ' (φ (χ (σ₂ (χ' P)))))
    rw [show φ' (φ (χ (σ₂ (χ' P)))) = χ (σ₂ (χ' P)) from DFunLike.congr_fun hi1 (χ (σ₂ (χ' P)))]
  have hA₂ : ∀ a' ∈ kernelIdealSet κ X₀ W₁' (ψ'.comp χ'), ∃ b' ∈ kernelIdealSet κ X₀ W₁ (ψ.comp χ),
      a' * (n : ↥(rationalEndSubring κ X₀)) = b' * s := by
    rintro a' ⟨ρ, hρ, hρa⟩
    obtain ⟨ρ₁, hρ₁, hρ₁eq⟩ := hF1 ρ hρ
    have hb : (ρ₁.comp ψ).comp χ ∈ rationalHomSet κ X₀ X₀ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W X₀ hχ (WeierstrassCurve.comp_mem_rationalHomSet κ W W₁ X₀ hψ hρ₁)
    refine ⟨⟨_, Subring.subset_closure hb⟩, ⟨_, hρ₁, rfl⟩, ?_⟩
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    show (a' : AddMonoid.End (Pt κ X₀)) (((n : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt κ X₀)) P) =
      ρ₁ (ψ (χ (σ₂ (χ' P))))
    rw [SubringClass.coe_intCast, AddMonoid.End.intCast_apply, hρa]
    show ρ (ψ' (χ' (n • P))) = ρ₁ (ψ (χ (σ₂ (χ' P))))
    rw [map_zsmul, ← hdual.comp_right (χ' P)]
    exact congrArg (fun f => f (χ (σ₂ (χ' P)))) hρ₁eq
  have hB₂ : ∀ b' ∈ kernelIdealSet κ X₀ W₁ (ψ.comp χ), ∃ a' ∈ kernelIdealSet κ X₀ W₁' (ψ'.comp χ'),
      b' * s = a' * (n : ↥(rationalEndSubring κ X₀)) := by
    rintro b' ⟨ρ, hρ, hρb⟩
    obtain ⟨ρ₁', hρ₁', hρ₁eq⟩ := hF2 ρ hρ
    have ha' : (ρ₁'.comp ψ').comp χ' ∈ rationalHomSet κ X₀ X₀ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W' X₀ hχ'
        (WeierstrassCurve.comp_mem_rationalHomSet κ W' W₁' X₀ hψ' hρ₁')
    refine ⟨⟨_, Subring.subset_closure ha'⟩, ⟨_, hρ₁', rfl⟩, ?_⟩
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    show (b' : AddMonoid.End (Pt κ X₀)) (σ₂ (χ' P)) =
      ρ₁' (ψ' (χ' (((n : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt κ X₀)) P)))
    rw [SubringClass.coe_intCast, AddMonoid.End.intCast_apply, hρb]
    show ρ (ψ (χ (σ₂ (χ' P)))) = ρ₁' (ψ' (χ' (n • P)))
    rw [map_zsmul, ← hdual.comp_right (χ' P)]
    show ρ (ψ (χ (σ₂ (χ' P)))) = ρ₁' (ψ' (φ (χ (σ₂ (χ' P)))))
    have := congrArg (fun f => f (φ (χ (σ₂ (χ' P))))) hρ₁eq
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
    rw [show φ' (φ (χ (σ₂ (χ' P)))) = χ (σ₂ (χ' P)) from DFunLike.congr_fun hi1 (χ (σ₂ (χ' P)))] at this
    exact this

  have hn0 : (n : ℍ[ℚ, a, b]) ≠ 0 := by
    intro h
    have h2 := congrArg QuaternionAlgebra.re h
    rw [QuaternionAlgebra.re_intCast] at h2
    have h3 : (n : ℚ) = 0 := h2
    exact hn.ne' (by exact_mod_cast h3)
  obtain ⟨un, hun⟩ := isUnit_of_ne_zero' ha hb hn0
  have hs0 : s ≠ 0 := by
    intro h0
    have hσ0 : σ₂ = 0 := by
      ext Q
      obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ' hχ'0 Q
      have := congrArg (fun t : ↥(rationalEndSubring κ X₀) => (t : AddMonoid.End (Pt κ X₀)) P) h0
      simp [hsdef] at this
      exact this
    apply smul_id_ne_zero (k := κ) X₀ hn.ne'
    ext P
    rw [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, ← hdual.comp_left P, hσ0,
      AddMonoidHom.zero_apply]
  have hθs0 : θ s ≠ 0 := fun h => hs0 (hθ (by rw [h, map_zero]))
  obtain ⟨us, hus⟩ := isUnit_of_ne_zero' ha hb hθs0
  refine ⟨us * un⁻¹, ?_, ?_⟩
  · ext z
    simp only [Set.mem_image, exists_exists_and_eq_and, Units.val_mul]
    constructor
    · rintro ⟨a', ha', rfl⟩
      obtain ⟨b', hb', hab⟩ := hA a' ha'
      refine ⟨b', hb', ?_⟩
      have h1 : θ a' * (n : ℍ[ℚ, a, b]) = θ b' * θ s := by
        rw [← map_intCast θ, ← map_mul, ← map_mul, hab]
      rw [hus, ← mul_assoc, ← h1, ← hun, Units.mul_inv_cancel_right]
    · rintro ⟨b', hb', rfl⟩
      obtain ⟨a', ha', hba⟩ := hB b' hb'
      refine ⟨a', ha', ?_⟩
      have h1 : θ b' * θ s = θ a' * (n : ℍ[ℚ, a, b]) := by
        rw [← map_intCast θ, ← map_mul, ← map_mul, hba]
      rw [hus, ← mul_assoc, h1, ← hun, Units.mul_inv_cancel_right]
  · ext z
    simp only [Set.mem_image, exists_exists_and_eq_and, Units.val_mul]
    constructor
    · rintro ⟨a', ha', rfl⟩
      obtain ⟨b', hb', hab⟩ := hA₂ a' ha'
      refine ⟨b', hb', ?_⟩
      have h1 : θ a' * (n : ℍ[ℚ, a, b]) = θ b' * θ s := by
        rw [← map_intCast θ, ← map_mul, ← map_mul, hab]
      rw [hus, ← mul_assoc, ← h1, ← hun, Units.mul_inv_cancel_right]
    · rintro ⟨b', hb', rfl⟩
      obtain ⟨a', ha', hba⟩ := hB₂ b' hb'
      refine ⟨a', ha', ?_⟩
      have h1 : θ b' * θ s = θ a' * (n : ℍ[ℚ, a, b]) := by
        rw [← map_intCast θ, ← map_mul, ← map_mul, hba]
      rw [hus, ← mul_assoc, h1, ← hun, Units.mul_inv_cancel_right]

end Backward

end CerednikDrinfeld.BrandtLevel
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld.BrandtLevel"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld"

open WeierstrassCurve CerednikDrinfeld.BrandtLevel in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (ha : a < 0) (hb : b < 0)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (W W' W₁ W₁' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic] [W₁.IsElliptic] [W₁'.IsElliptic]
    (χ : X₀.toAffine.Point →+ W.toAffine.Point) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : X₀.toAffine.Point →+ W'.toAffine.Point) (hχ' : χ' ∈ WeierstrassCurve.rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0)
    (N : ℕ) (hN0 : N ≠ 0) (hNκ : (N : κ) ≠ 0)
    (ψ : W.toAffine.Point →+ W₁.toAffine.Point) (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W₁)
    (ψd : W₁.toAffine.Point →+ W.toAffine.Point) (hψd : ψd ∈ WeierstrassCurve.rationalHomSet κ W₁ W)
    (hψ1 : ψd.comp ψ = N • AddMonoidHom.id _) (hψ2 : ψ.comp ψd = N • AddMonoidHom.id _)
    (hψN : Nat.card ψ.ker = N)
    (ψ' : W'.toAffine.Point →+ W₁'.toAffine.Point) (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W₁')
    (ψd' : W₁'.toAffine.Point →+ W'.toAffine.Point) (hψd' : ψd' ∈ WeierstrassCurve.rationalHomSet κ W₁' W')
    (hψ'1 : ψd'.comp ψ' = N • AddMonoidHom.id _) (hψ'2 : ψ'.comp ψd' = N • AddMonoidHom.id _)
    (hψ'N : Nat.card ψ'.ker = N)
    (φ : W.toAffine.Point →+ W'.toAffine.Point) (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ W W')
    (φ' : W'.toAffine.Point →+ W.toAffine.Point) (hφ' : φ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (hi1 : φ'.comp φ = AddMonoidHom.id _) (hi2 : φ.comp φ' = AddMonoidHom.id _)
    (hlev : ∀ T ∈ ψ.ker, φ T ∈ ψ'.ker) :
    ∃ c : (ℍ[ℚ, a, b])ˣ,
      θ '' WeierstrassCurve.kernelIdealSet κ X₀ W' χ' =
          (· * (c : ℍ[ℚ, a, b])) '' (θ '' WeierstrassCurve.kernelIdealSet κ X₀ W χ) ∧
        θ '' WeierstrassCurve.kernelIdealSet κ X₀ W₁' (ψ'.comp χ') =
          (· * (c : ℍ[ℚ, a, b])) '' (θ '' WeierstrassCurve.kernelIdealSet κ X₀ W₁ (ψ.comp χ)) :=
  exists_units_image_pair_of_iso q' hss ha hb θ hθ hχ hχ0 hχ' hχ'0 hN0 hNκ hψ hψd hψ1 hψ2 hψN hψ' hψd' hψ'1 hψ'2 hψ'N
    hφ hφ' hi1 hi2 hlev

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld.BrandtLevel"

end S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker
end P2MW
export P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker (solution)
