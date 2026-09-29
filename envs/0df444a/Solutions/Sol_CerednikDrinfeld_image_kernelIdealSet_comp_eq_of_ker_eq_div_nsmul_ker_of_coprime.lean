-- Prove2me | solution 1 for CerednikDrinfeld.image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/52108831-507f-5867-8743-a52207dc28bf

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime.CerednikDrinfeld ModularCurve AlgebraicCurve IsDedekindDomain"

noncomputable section

namespace CerednikDrinfeld
namespace HeartC
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

end Points

section Quaternion

variable {a b : ℚ}

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

end Frame

section Glue

open WeierstrassCurve

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem smul_mem_ofFiniteIdele_of_smul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {g g' k : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ} (hg : g' = g * k) (c : ℚ)
    (hc : c • ((k : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ g') :
    c • z ∈ Submodule.ofFiniteIdele Λ g := by
  subst hg
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨(c • ((k : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) * w, mul_mem_finiteAdeleBox hΛ hc hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [Units.val_mul, mul_assoc] at hwz
  rw [smul_mul_assoc, mul_smul_comm, hwz, TensorProduct.smul_tmul']

theorem mem_ofFiniteIdele_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {g g' k : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ} (hg : g' = g * k)
    (hk : ((k : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ g') :
    z ∈ Submodule.ofFiniteIdele Λ g := by
  have h := smul_mem_ofFiniteIdele_of_smul_mem hΛ hg (1 : ℚ) (by rw [one_smul]; exact hk) hz
  rwa [one_smul] at h

theorem mem_of_coprime_of_smul_mem (K : Submodule ℤ ℍ[ℚ, a, b]) {M N : ℕ} (h : Nat.Coprime M N)
    {z : ℍ[ℚ, a, b]} (hM : ((M : ℕ) : ℚ) • z ∈ K) (hN : ((N : ℕ) : ℚ) • z ∈ K) : z ∈ K := by
  have hb := Nat.gcd_eq_gcd_ab M N
  rw [Nat.Coprime.gcd_eq_one h, Nat.cast_one] at hb
  have hM' : (M : ℤ) • z ∈ K := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]; exact hM
  have hN' : (N : ℤ) • z ∈ K := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]; exact hN
  have key : ((M : ℤ) * Nat.gcdA M N + (N : ℤ) * Nat.gcdB M N) • z = z := by
    rw [← hb, one_smul]
  rw [← key, add_smul, mul_comm (M : ℤ), mul_comm (N : ℤ), mul_smul, mul_smul]
  exact K.add_mem (K.smul_mem _ hM') (K.smul_mem _ hN')

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]
variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]} {χ : Pt κ X₀ →+ Pt κ W}
  {d : (ℍ[ℚ, a, b])ˣ} {x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ}

theorem IsKernelFrame.image_kernelIdealSet_comp_eq_latOf (hF : IsKernelFrame Λ θ χ d x)
    {V : WeierstrassCurve κ} [V.IsElliptic] {π : Pt κ W →+ Pt κ V} (hπ : π ∈ rationalHomSet κ W V)
    (huniv : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : Pt κ W →+ Pt κ V'),
      α ∈ rationalHomSet κ W V' → π.ker ≤ α.ker → ∃ β ∈ rationalHomSet κ V V', α = β.comp π) :
    θ '' (kernelIdealSet κ X₀ V (π.comp χ)) =
      star '' ((d • latOf θ hF.mem d π.ker : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  ext w
  constructor
  · rintro ⟨e, ⟨ρ', hρ', he⟩, rfl⟩
    have hρ : ρ'.comp π ∈ rationalHomSet κ W X₀ := comp_mem_rationalHomSet κ W V X₀ hπ hρ'
    have hρU : π.ker ≤ (ρ'.comp π).ker := fun P hP => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, show π P = 0 from hP, map_zero]
    have hce : compEnd hF.mem ⟨ρ'.comp π, hρ⟩ = e := Subtype.ext (by rw [coe_compEnd, he]; rfl)
    refine ⟨(d : ℍ[ℚ, a, b]) * tr θ hF.mem d ⟨ρ'.comp π, hρ⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_units_smul_iff, ← mul_assoc, Units.inv_mul, one_mul]
      exact (mem_latOf_iff θ hF.mem d _ _).mpr ⟨⟨ρ'.comp π, hρ⟩, hρU, rfl⟩
    · rw [← theta_compEnd_eq, hce]
  · rintro ⟨w', hw', rfl⟩
    rw [SetLike.mem_coe, mem_units_smul_iff] at hw'
    obtain ⟨ρ, hρU, hρ⟩ := (mem_latOf_iff θ hF.mem d _ _).mp hw'
    obtain ⟨ρV, hρV, hρeq⟩ := huniv X₀ ρ.1 ρ.2 hρU
    refine ⟨compEnd hF.mem ρ, ⟨ρV, hρV, by rw [coe_compEnd, hρeq]; rfl⟩, ?_⟩
    rw [theta_compEnd_eq θ hF.mem d ρ, hρ, ← mul_assoc, Units.mul_inv, one_mul]

theorem main
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic]
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : Pt κ X₁ →+ Pt κ W)
    (hχ : χ ∈ rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (L : ℕ) (hq'L : ¬ q' ∣ L) (m' : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : Pt κ W →+ Pt κ W')
    (hψ : ψ ∈ rationalHomSet κ W W')
    (ψ' : Pt κ W' →+ Pt κ W) (hψ' : ψ' ∈ rationalHomSet κ W' W)
    (hψ'ψ : ψ'.comp ψ = (L : ℕ) • AddMonoidHom.id _) (hψψ' : ψ.comp ψ' = (L : ℕ) • AddMonoidHom.id _)
    (hK' : θ₁ '' kernelIdealSet κ X₁ W' (ψ.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (M : ℕ) (hML : M ∣ L) (hcop : Nat.Coprime M (L / M))
    (m'' : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (hm''₁ : ((m'' : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm''m' : ((m''⁻¹ * m' : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm''M : ((M : ℕ) : ℚ) • ((m''⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'm'' : ((L / M : ℕ) : ℚ) • ((m'⁻¹ * m'' : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
      Submodule.finiteAdeleBox Λ₁)
    (V : WeierstrassCurve κ) [V.IsElliptic] (π : Pt κ W →+ Pt κ V)
    (hπ : π ∈ rationalHomSet κ W V)
    (hπker : ∀ T : Pt κ W, T ∈ π.ker ↔ ∃ S ∈ ψ.ker, (L / M) • S = T)
    (hπuniv : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : Pt κ W →+ Pt κ V'),
      α ∈ rationalHomSet κ W V' → π.ker ≤ α.ker → ∃ β ∈ rationalHomSet κ V V', α = β.comp π) :
    θ₁ '' kernelIdealSet κ X₁ V (π.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m'') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  classical
  have hF : IsKernelFrame Λ₁ θ₁ χ d x := ⟨hΛ₁.isOrder, hθ₁, hθ₁Λ, hχ, hχ0, hK⟩
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact hq'L (dvd_zero _)
  have hLκ : (L : κ) ≠ 0 := fun h => hq'L ((CharP.cast_eq_zero_iff κ q' L).mp h)

  have hLS : ∀ S : Pt κ W, L • S = ψ' (ψ S) := fun S => by
    have h := DFunLike.congr_fun hψ'ψ S
    rw [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply] at h
    exact h.symm
  have hkerψ : ∀ S : Pt κ W, S ∈ ψ.ker → (L / M) • S ∈ π.ker := fun S hS => (hπker _).mpr ⟨S, hS, rfl⟩
  have hkerle : π.ker ≤ ψ.ker := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := (hπker T).mp hT
    rw [AddMonoidHom.mem_ker, map_nsmul, show ψ S = 0 from hS, smul_zero]

  rw [hF.image_kernelIdealSet_comp_eq_latOf hπ hπuniv]
  set J : Submodule ℤ ℍ[ℚ, a, b] := latOf θ₁ hF.mem d π.ker with hJdef
  suffices hJ : J = Submodule.ofFiniteIdele Λ₁ (x * m'') by rw [hJ]

  have hI1 : Submodule.ofFiniteIdele Λ₁ (x * m') ≤ J := by
    intro z hz
    have h1 : star ((d : ℍ[ℚ, a, b]) * z) ∈ θ₁ '' kernelIdealSet κ X₁ W' (ψ.comp χ) := by
      rw [hK']
      refine ⟨(d : ℍ[ℚ, a, b]) * z, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_units_smul_iff, ← mul_assoc, Units.inv_mul, one_mul]
      exact hz
    obtain ⟨e, ⟨ρ', hρ', he⟩, he'⟩ := h1
    have hρ : ρ'.comp ψ ∈ rationalHomSet κ W X₁ := comp_mem_rationalHomSet κ W W' X₁ hψ hρ'
    refine (mem_latOf_iff θ₁ hF.mem d _ z).mpr ⟨⟨ρ'.comp ψ, hρ⟩, ?_, ?_⟩
    · intro T hT
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, show ψ T = 0 from hkerle hT, map_zero]
    · have hce : compEnd hF.mem ⟨ρ'.comp ψ, hρ⟩ = e := Subtype.ext (by rw [coe_compEnd, he]; rfl)
      rw [tr_apply, hce, he', star_star, ← mul_assoc, Units.inv_mul, one_mul]

  have hI2 : J ≤ Submodule.ofFiniteIdele Λ₁ x := by
    intro z hz
    obtain ⟨ρ, -, rfl⟩ := (mem_latOf_iff θ₁ hF.mem d _ z).mp hz
    exact hF.tr_mem ρ

  have hI3 : ∀ z ∈ Submodule.ofFiniteIdele Λ₁ x, ((M : ℕ) : ℚ) • z ∈ J := by
    intro z hz
    obtain ⟨ρ, rfl⟩ := hF.exists_tr_eq hz
    refine (mem_latOf_iff θ₁ hF.mem d _ _).mpr ⟨M • ρ, ?_, ?_⟩
    · intro T hT
      obtain ⟨S, hS, rfl⟩ := (hπker T).mp hT
      have hc : ((M • ρ : homGrp W X₁) : Pt κ W →+ Pt κ X₁) = M • (ρ : Pt κ W →+ Pt κ X₁) := rfl
      rw [AddMonoidHom.mem_ker, hc, AddMonoidHom.nsmul_apply, ← map_nsmul, smul_smul,
        Nat.mul_div_cancel' hML, hLS S, show ψ S = 0 from hS, map_zero, map_zero]
    · rw [map_nsmul, Nat.cast_smul_eq_nsmul]

  have hI4 : ∀ z ∈ J, ((L / M : ℕ) : ℚ) • z ∈ Submodule.ofFiniteIdele Λ₁ (x * m') := by
    intro z hz
    obtain ⟨ρ, hρU, rfl⟩ := (mem_latOf_iff θ₁ hF.mem d _ _).mp hz

    have hβ : ((L / M) • ρ.1).comp ψ' ∈ rationalHomSet κ W' X₁ :=
      comp_mem_rationalHomSet κ W' W X₁ hψ' (nsmul_mem_rationalHomSet ρ.2 _)
    have hβker : ∀ P : Pt κ W', (L : ℤ) • P = 0 → ((L / M) • ρ.1).comp ψ' P = 0 := by
      intro P hP
      have hS : ψ' P ∈ ψ.ker := by
        have h := DFunLike.congr_fun hψψ' P
        rw [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, ← natCast_zsmul,
          hP] at h
        exact h
      rw [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, ← map_nsmul]
      exact hρU (hkerψ _ hS)
    obtain ⟨σ, hσ, hσeq⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W' X₁ hLκ hβ hβker
    have hσψ : σ.comp ψ ∈ rationalHomSet κ W X₁ := comp_mem_rationalHomSet κ W W' X₁ hψ hσ

    have hcancel : (L / M) • ρ.1 = σ.comp ψ := by
      have hdiff : L • ((L / M) • ρ.1 - σ.comp ψ) = 0 := by
        ext P
        have h1 : ((L / M) • ρ.1).comp ψ' (ψ P) = (L : ℤ) • σ (ψ P) := hσeq (ψ P)
        rw [AddMonoidHom.comp_apply, ← hLS P, map_nsmul] at h1
        rw [AddMonoidHom.nsmul_apply, AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, smul_sub, sub_eq_zero,
          AddMonoidHom.comp_apply, h1, natCast_zsmul]
      exact sub_eq_zero.mp
        (eq_zero_of_nsmul_eq_zero (sub_mem_rationalHomSet (nsmul_mem_rationalHomSet ρ.2 _) hσψ) hL0 hLκ hdiff)
    have htr : ((L / M : ℕ) : ℚ) • tr θ₁ hF.mem d ρ = tr θ₁ hF.mem d ⟨σ.comp ψ, hσψ⟩ := by
      have h2 : (⟨σ.comp ψ, hσψ⟩ : homGrp W X₁) = (L / M) • ρ := Subtype.ext hcancel.symm
      rw [h2, map_nsmul, Nat.cast_smul_eq_nsmul]
    rw [htr]
    have hmem : θ₁ (compEnd hF.mem ⟨σ.comp ψ, hσψ⟩) ∈ θ₁ '' kernelIdealSet κ X₁ W' (ψ.comp χ) :=
      ⟨_, ⟨σ, hσ, by rw [coe_compEnd]; rfl⟩, rfl⟩
    rw [hK'] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    rw [SetLike.mem_coe, mem_units_smul_iff] at hw
    rw [tr_apply, ← hw', star_star]
    exact hw

  have hK1 : Submodule.ofFiniteIdele Λ₁ (x * m') ≤ Submodule.ofFiniteIdele Λ₁ (x * m'') := fun z hz =>
    mem_ofFiniteIdele_of_mem hΛ₁.isOrder (by rw [mul_assoc, mul_inv_cancel_left]) hm''m' hz
  have hK2 : Submodule.ofFiniteIdele Λ₁ (x * m'') ≤ Submodule.ofFiniteIdele Λ₁ x := fun z hz =>
    mem_ofFiniteIdele_of_mem hΛ₁.isOrder rfl hm''₁ hz
  have hK3 : ∀ z ∈ Submodule.ofFiniteIdele Λ₁ x, ((M : ℕ) : ℚ) • z ∈ Submodule.ofFiniteIdele Λ₁ (x * m'') :=
    fun z hz => smul_mem_ofFiniteIdele_of_smul_mem hΛ₁.isOrder (by rw [mul_inv_cancel_right]) _ hm''M hz
  have hK4 : ∀ z ∈ Submodule.ofFiniteIdele Λ₁ (x * m''),
      ((L / M : ℕ) : ℚ) • z ∈ Submodule.ofFiniteIdele Λ₁ (x * m') :=
    fun z hz => smul_mem_ofFiniteIdele_of_smul_mem hΛ₁.isOrder (by rw [mul_assoc, mul_inv_cancel_left]) _ hm'm'' hz

  apply le_antisymm
  · intro z hz
    exact mem_of_coprime_of_smul_mem _ hcop (hK3 z (hI2 hz)) (hK1 (hI4 z hz))
  · intro z hz
    exact mem_of_coprime_of_smul_mem _ hcop (hI3 z (hK2 hz)) (hI1 (hK4 z hz))

end Glue

end CerednikDrinfeld.HeartC
p2m_reactivate "P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime.CerednikDrinfeld P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime.CerednikDrinfeld.HeartC"
p2m_reactivate "P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime.CerednikDrinfeld P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime.CerednikDrinfeld.HeartC"

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
    (L : ℕ) (hq'L : ¬ q' ∣ L) (m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
    (ψ' : W'.toAffine.Point →+ W.toAffine.Point) (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (hψ'ψ : ψ'.comp ψ = (L : ℕ) • AddMonoidHom.id _) (hψψ' : ψ.comp ψ' = (L : ℕ) • AddMonoidHom.id _)
    (hK' : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (M : ℕ) (hML : M ∣ L) (hcop : Nat.Coprime M (L / M))
    (m'' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm''₁ : ((m'' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm''m' : ((m''⁻¹ * m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm''M : ((M : ℕ) : ℚ) • ((m''⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'm'' : ((L / M : ℕ) : ℚ) • ((m'⁻¹ * m'' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (V : WeierstrassCurve κ) [V.IsElliptic] (π : W.toAffine.Point →+ V.toAffine.Point)
    (hπ : π ∈ WeierstrassCurve.rationalHomSet κ W V)
    (hπker : ∀ T : W.toAffine.Point, T ∈ π.ker ↔ ∃ S ∈ ψ.ker, (L / M) • S = T)
    (hπuniv : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : W.toAffine.Point →+ V'.toAffine.Point),
      α ∈ WeierstrassCurve.rationalHomSet κ W V' → π.ker ≤ α.ker →
        ∃ β ∈ WeierstrassCurve.rationalHomSet κ V V', α = β.comp π) :
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V (π.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m'') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  exact
    CerednikDrinfeld.HeartC.main q' X₁ Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ x W χ hχ hχ0 d hK L hq'L m' W' ψ hψ ψ' hψ' hψ'ψ hψψ' hK' M hML
    hcop m'' hm''₁ hm''m' hm''M hm'm'' V π hπ hπker hπuniv

end S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime
end P2MW
export P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime (solution)
