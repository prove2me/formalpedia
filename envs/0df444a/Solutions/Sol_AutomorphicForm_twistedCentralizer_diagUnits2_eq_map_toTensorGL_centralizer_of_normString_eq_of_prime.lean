-- Prove2me | solution 1 for AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c8089a5a-48ed-5c8b-9138-5ee501ebd9a1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mTwistedTorus

section Fixed

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [Field A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (x : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ x) = σ l ⊗ₜ x := rfl

theorem sigmaTensor_one_tmul (x : A) :
    AutomorphicForm.sigmaTensor K L A σ ((1 : L) ⊗ₜ x) = (1 : L) ⊗ₜ x := by
  rw [sigmaTensor_tmul, map_one]

abbrev T : L →ₗ[K] L := (σ : L →ₐ[K] L).toLinearMap - LinearMap.id

theorem rTensor_T_apply (x : L ⊗[K] A) :
    (T K L σ).rTensor A x = AutomorphicForm.sigmaTensor K L A σ x - x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [LinearMap.rTensor_tmul, sigmaTensor_tmul]; simp [TensorProduct.sub_tmul]
  | add x y hx hy => rw [map_add, hx, hy, map_add]; abel

variable (hprime : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
include hprime hσ

theorem exists_algebraMap_eq_of_fixed (l : L) (hl : σ l = l) : ∃ k : K, algebraMap K L k = l := by
  obtain ⟨hgal, -, htop⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  haveI := hgal
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
  rw [← Set.mem_range, IsGalois.mem_range_algebraMap_iff_fixed]
  intro f
  have hf : f ∈ Subgroup.zpowers σ := by rw [htop]; exact Subgroup.mem_top f
  have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) l :=
    Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hl)
  exact hstab hf

theorem exists_eq_one_tmul_of_fixed (x : L ⊗[K] A) (hx : AutomorphicForm.sigmaTensor K L A σ x = x) :
    ∃ y : A, x = (1 : L) ⊗ₜ y := by

  have hker : (T K L σ).rTensor A x = 0 := by rw [rTensor_T_apply, hx, sub_self]
  have hexact := Module.Flat.rTensor_exact A (LinearMap.exact_subtype_ker_map (T K L σ))
  obtain ⟨z, hz⟩ := (hexact x).1 hker

  have hkerT : ∀ l : LinearMap.ker (T K L σ), ∃ k : K, algebraMap K L k = (l : L) := fun l => by
    apply exists_algebraMap_eq_of_fixed K L σ hprime hσ
    have h2 := LinearMap.mem_ker.1 l.2
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h2
    exact h2
  choose φ hφ using hkerT
  have hφ_lin : ∀ (l l' : LinearMap.ker (T K L σ)) (k : K), φ (l + l') = φ l + φ l' ∧ φ (k • l) = k * φ l := by
    intro l l' k
    constructor
    · apply (algebraMap K L).injective
      rw [map_add, hφ, hφ, hφ]; rfl
    · apply (algebraMap K L).injective
      rw [map_mul, hφ, hφ, Submodule.coe_smul, Algebra.smul_def]
  let φl : LinearMap.ker (T K L σ) →ₗ[K] K :=
    { toFun := φ, map_add' := fun l l' => (hφ_lin l l' 1).1, map_smul' := fun k l => (hφ_lin l l k).2 }
  have key : ∀ z : LinearMap.ker (T K L σ) ⊗[K] A,
      (LinearMap.ker (T K L σ)).subtype.rTensor A z = (1 : L) ⊗ₜ TensorProduct.lid K A (φl.rTensor A z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
        rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Submodule.subtype_apply]
        conv_lhs => rw [← hφ l, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        rfl
    | add x y hx hy => rw [map_add, map_add, map_add, TensorProduct.tmul_add, ← hx, ← hy]
  exact ⟨TensorProduct.lid K A (φl.rTensor A z), by rw [← hz, key]⟩

end Fixed

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaGL_apply (t : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (AutomorphicForm.sigmaGL K L A σ t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := rfl

theorem sigmaGL_iterate_apply (k : ℕ) (t : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(AutomorphicForm.sigmaGL K L A σ))^[k] t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[k] ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sigmaGL_apply, ih]

theorem toTensorGL_apply (s : GL (Fin 2) A) (i j : Fin 2) :
    (AutomorphicForm.toTensorGL K L A s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ ((s : Matrix (Fin 2) (Fin 2) A) i j) := rfl

def P (δ : GL (Fin 2) (L ⊗[K] A)) (k : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range k).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod

theorem P_succ (δ : GL (Fin 2) (L ⊗[K] A)) (k : ℕ) :
    P K L A σ δ (k + 1) = P K L A σ δ k * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ := by
  unfold P
  rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

theorem normString_eq_P (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem mul_P_eq (δ t : GL (Fin 2) (L ⊗[K] A)) (h : t * δ = δ * AutomorphicForm.sigmaGL K L A σ t) (k : ℕ) :
    t * P K L A σ δ k = P K L A σ δ k * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] t := by
  induction k with
  | zero => simp [P]
  | succ k ih =>
      have hk : (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] t * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ =
          (⇑(AutomorphicForm.sigmaGL K L A σ))^[k] δ * (⇑(AutomorphicForm.sigmaGL K L A σ))^[k + 1] t := by
        rw [← iterate_map_mul, h, iterate_map_mul, Function.iterate_succ_apply]
      rw [P_succ, ← mul_assoc, ih, mul_assoc, hk, ← mul_assoc]

end NormString

section Iterate

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [Field A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_iterate_tmul (k : ℕ) (l : L) (a : A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[k] (l ⊗ₜ a) = (σ ^ k) l ⊗ₜ a := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, sigmaTensor_tmul, pow_succ', AlgEquiv.mul_apply]

variable (hprime : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
include hprime hσ

theorem sigmaTensor_iterate_finrank (x : L ⊗[K] A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[Module.finrank K L] x = x := by
  obtain ⟨-, hord, -⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  induction x using TensorProduct.induction_on with
  | zero => exact iterate_map_zero _ _
  | tmul l a => rw [sigmaTensor_iterate_tmul, ← hord, pow_orderOf_eq_one, AlgEquiv.one_apply]
  | add x y hx hy => rw [iterate_map_add, hx, hy]

theorem sigmaGL_iterate_finrank (t : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(AutomorphicForm.sigmaGL K L A σ))^[Module.finrank K L] t = t := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate_finrank K L A σ hprime hσ]

end Iterate

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [Field A] [Algebra K A]
  (σ : L ≃ₐ[K] L) (hprime : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
  (a b : Aˣ) (hab : a ≠ b) (α β : (L ⊗[K] A)ˣ)
  (hN : AutomorphicForm.normString K L A σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L A (diagUnits2 a b))

local notation "E" => L ⊗[K] A
local notation "ι" => (fun y : A => (1 : L) ⊗ₜ[K] y)

theorem includeRight_injective' : Function.Injective (fun y : A => ((1 : L) ⊗ₜ[K] y : E)) := by
  have h := Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := A) (algebraMap K L).injective
  intro y y' hyy'
  exact h hyy'

include hab in
theorem isUnit_one_tmul_sub : IsUnit ((1 : L) ⊗ₜ[K] ((b : A) - a) : E) := by
  have hne : (b : A) - a ≠ 0 := sub_ne_zero.2 fun h => hab (Units.ext h).symm
  exact (isUnit_iff_ne_zero.2 hne).map (Algebra.TensorProduct.includeRight : A →ₐ[K] E)

theorem diagUnits2_apply_00 {R : Type} [CommRing R] (x y : Rˣ) :
    ((diagUnits2 x y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = x := rfl
theorem diagUnits2_apply_01 {R : Type} [CommRing R] (x y : Rˣ) :
    ((diagUnits2 x y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := rfl
theorem diagUnits2_apply_10 {R : Type} [CommRing R] (x y : Rˣ) :
    ((diagUnits2 x y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := rfl
theorem diagUnits2_apply_11 {R : Type} [CommRing R] (x y : Rˣ) :
    ((diagUnits2 x y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = y := rfl

theorem offdiag_eq_zero_of_commute {R : Type} [CommRing R] (x y : Rˣ) (hxy : IsUnit ((y : R) - x))
    (M : Matrix (Fin 2) (Fin 2) R)
    (h : M * ((diagUnits2 x y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      ((diagUnits2 x y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * M) :
    M 0 1 = 0 ∧ M 1 0 = 0 := by
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, diagUnits2_apply_00, diagUnits2_apply_01, diagUnits2_apply_10,
    diagUnits2_apply_11, mul_zero, zero_mul, add_zero, zero_add] at h01 h10
  obtain ⟨u, hu⟩ := hxy
  constructor
  · have : M 0 1 * ((y : R) - x) = 0 := by rw [mul_sub, h01, mul_comm (x : R) (M 0 1), sub_self]
    rw [← hu] at this
    exact (Units.mul_left_eq_zero u).1 this
  · have : M 1 0 * ((y : R) - x) = 0 := by rw [mul_sub, h10, mul_comm (y : R) (M 1 0), sub_self]
    rw [← hu] at this
    exact (Units.mul_left_eq_zero u).1 this

include hprime hσ hab hN

theorem subset (t : GL (Fin 2) E) (ht : t ∈ AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 α β)) :
    t ∈ (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A) := by
  set δ : GL (Fin 2) E := diagUnits2 α β with hδ
  set γE : GL (Fin 2) E := AutomorphicForm.toTensorGL K L A (diagUnits2 a b) with hγE
  have ht' : t * δ = δ * AutomorphicForm.sigmaGL K L A σ t := by
    have := (AutomorphicForm.mem_sigmaCentralizer_iff).1 ht
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this

  have hcomm : t * γE = γE * t := by
    have h := mul_P_eq K L A σ δ t ht' (Module.finrank K L)
    rw [← normString_eq_P, sigmaGL_iterate_finrank K L A σ hprime hσ, hδ, hN] at h
    exact h

  have hcommM : (t : Matrix (Fin 2) (Fin 2) E) * (γE : Matrix (Fin 2) (Fin 2) E) =
      (γE : Matrix (Fin 2) (Fin 2) E) * (t : Matrix (Fin 2) (Fin 2) E) := by
    rw [← Units.val_mul, hcomm, Units.val_mul]
  have hγ00 : (γE : Matrix (Fin 2) (Fin 2) E) 0 0 = (1 : L) ⊗ₜ (a : A) := rfl
  have hγ11 : (γE : Matrix (Fin 2) (Fin 2) E) 1 1 = (1 : L) ⊗ₜ (b : A) := rfl
  have hγ01 : (γE : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by
    rw [hγE, toTensorGL_apply, diagUnits2_apply_01, TensorProduct.tmul_zero]
  have hγ10 : (γE : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
    rw [hγE, toTensorGL_apply, diagUnits2_apply_10, TensorProduct.tmul_zero]
  have h01 := congrFun (congrFun hcommM 0) 1
  have h10 := congrFun (congrFun hcommM 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hγ00, hγ01, hγ10, hγ11, mul_zero, zero_mul, add_zero, zero_add]
    at h01 h10
  obtain ⟨u, hu⟩ := isUnit_one_tmul_sub K L A a b hab
  have hu' : (u : E) = (1 : L) ⊗ₜ (b : A) - (1 : L) ⊗ₜ (a : A) := by rw [hu, TensorProduct.tmul_sub]
  have ht01 : (t : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by
    have : (t : Matrix (Fin 2) (Fin 2) E) 0 1 * ((1 : L) ⊗ₜ (b : A) - (1 : L) ⊗ₜ (a : A)) = 0 := by
      rw [mul_sub, h01, mul_comm ((1 : L) ⊗ₜ[K] (a : A)) ((t : Matrix (Fin 2) (Fin 2) E) 0 1), sub_self]
    rw [← hu'] at this
    exact (Units.mul_left_eq_zero u).1 this
  have ht10 : (t : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
    have : (t : Matrix (Fin 2) (Fin 2) E) 1 0 * ((1 : L) ⊗ₜ (b : A) - (1 : L) ⊗ₜ (a : A)) = 0 := by
      rw [mul_sub, h10, mul_comm ((1 : L) ⊗ₜ[K] (b : A)) ((t : Matrix (Fin 2) (Fin 2) E) 1 0), sub_self]
    rw [← hu'] at this
    exact (Units.mul_left_eq_zero u).1 this

  have htδ : (t : Matrix (Fin 2) (Fin 2) E) * (δ : Matrix (Fin 2) (Fin 2) E) =
      (δ : Matrix (Fin 2) (Fin 2) E) * (AutomorphicForm.sigmaGL K L A σ t : Matrix (Fin 2) (Fin 2) E) := by
    rw [← Units.val_mul, ht', Units.val_mul]
  have h00 := congrFun (congrFun htδ 0) 0
  have h11 := congrFun (congrFun htδ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hδ, diagUnits2_apply_00, diagUnits2_apply_01,
    diagUnits2_apply_10, diagUnits2_apply_11, sigmaGL_apply, mul_zero, zero_mul, add_zero, zero_add] at h00 h11
  have hfix0 : AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 0 0) =
      (t : Matrix (Fin 2) (Fin 2) E) 0 0 := by
    have : (α : E) * AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 0 0) =
        (α : E) * (t : Matrix (Fin 2) (Fin 2) E) 0 0 := by rw [← h00, mul_comm]
    exact (Units.mul_right_inj α).1 this
  have hfix1 : AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 1 1) =
      (t : Matrix (Fin 2) (Fin 2) E) 1 1 := by
    have : (β : E) * AutomorphicForm.sigmaTensor K L A σ ((t : Matrix (Fin 2) (Fin 2) E) 1 1) =
        (β : E) * (t : Matrix (Fin 2) (Fin 2) E) 1 1 := by rw [← h11, mul_comm]
    exact (Units.mul_right_inj β).1 this
  obtain ⟨y₀, hy₀⟩ := exists_eq_one_tmul_of_fixed K L A σ hprime hσ _ hfix0
  obtain ⟨y₁, hy₁⟩ := exists_eq_one_tmul_of_fixed K L A σ hprime hσ _ hfix1

  have hdet : IsUnit ((t : Matrix (Fin 2) (Fin 2) E).det) := Matrix.isUnits_det_units t
  rw [Matrix.det_fin_two, ht01, zero_mul, sub_zero, hy₀, hy₁, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at hdet
  haveI : Nontrivial E := (includeRight_injective' K L A).nontrivial
  have hy0 : y₀ ≠ 0 := by
    intro h; rw [h, zero_mul, TensorProduct.tmul_zero] at hdet; exact not_isUnit_zero hdet
  have hy1 : y₁ ≠ 0 := by
    intro h; rw [h, mul_zero, TensorProduct.tmul_zero] at hdet; exact not_isUnit_zero hdet

  refine Subgroup.mem_map.2 ⟨diagUnits2 (Units.mk0 y₀ hy0) (Units.mk0 y₁ hy1), ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, LanglandsTunnell.CubicInduction.coe_diagUnits2, mul_comm]
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [toTensorGL_apply]
    fin_cases i <;> fin_cases j
    · change (1 : L) ⊗ₜ y₀ = (t : Matrix (Fin 2) (Fin 2) E) 0 0; rw [hy₀]
    · change (1 : L) ⊗ₜ (0 : A) = (t : Matrix (Fin 2) (Fin 2) E) 0 1; rw [ht01, TensorProduct.tmul_zero]
    · change (1 : L) ⊗ₜ (0 : A) = (t : Matrix (Fin 2) (Fin 2) E) 1 0; rw [ht10, TensorProduct.tmul_zero]
    · change (1 : L) ⊗ₜ y₁ = (t : Matrix (Fin 2) (Fin 2) E) 1 1; rw [hy₁]

omit hprime hσ hN in

theorem superset (t : GL (Fin 2) E)
    (ht : t ∈ (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 α β) := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
  rw [Subgroup.mem_centralizer_singleton_iff] at hs
  have hsM : (s : Matrix (Fin 2) (Fin 2) A) * ((diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      ((diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * s := by
    rw [← Units.val_mul, hs, Units.val_mul]
  have hba : IsUnit ((b : A) - a) := isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h).symm)
  obtain ⟨hs01, hs10⟩ := offdiag_eq_zero_of_commute a b hba _ hsM

  have hσs : AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A s) = AutomorphicForm.toTensorGL K L A s := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_one_tmul]
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, hσs, mul_inv_eq_iff_eq_mul]

  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, toTensorGL_apply, hs01, hs10,
      LanglandsTunnell.CubicInduction.coe_diagUnits2, mul_comm]

theorem main :
    AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 α β) =
      (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A) := by
  ext t
  exact ⟨subset K L A σ hprime hσ a b hab α β hN t, superset K L A σ a b hab α β t⟩

end Main

end P2mTwistedTorus

end

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [Field A] [Algebra K A]
    (a b : Aˣ) (hab : a ≠ b) (α β : (L ⊗[K] A)ˣ)
    (hN : AutomorphicForm.normString K L A σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 α β) =
      (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A) :=
  P2mTwistedTorus.main K L A σ hprime hσ a b hab α β hN

end S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
end P2MW
export P2MW.S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime (solution)
