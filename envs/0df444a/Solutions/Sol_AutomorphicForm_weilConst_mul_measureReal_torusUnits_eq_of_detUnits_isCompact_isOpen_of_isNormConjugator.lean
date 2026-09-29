-- Prove2me | solution 1 for AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e39c6b1c-3fbb-53c8-a551-a014ee6dbbe1

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory TopologicalSpace Topology Filter Set MulAction
open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mFinUnits

section Algebra

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

end Algebra

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "sT" => AutomorphicForm.sigmaTensor K L A σ
local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "ι" => AutomorphicForm.toTensorGL K L A
local notation "incl" => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)

theorem sigmaTensor_tmul (l : L) (a : A) : sT (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_one_tmul (a : A) : sT ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
  rw [sigmaTensor_tmul, map_one]

theorem sigmaTensor_includeRight (a : A) : sT (incl a) = incl a :=
  sigmaTensor_one_tmul K L A σ a

theorem sigmaTensor_sigmaTensor (hσ : ∀ l : L, σ (σ l) = l) (b : L ⊗[K] A) : sT (sT b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigmaGL_apply (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sT ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem coe_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map sT := by
  ext i j
  exact sigmaGL_apply K L A σ g i j

theorem sigmaGL_sigmaGL (hσ : ∀ l : L, σ (σ l) = l) (g : GL (Fin 2) (L ⊗[K] A)) : sG (sG g) = g := by
  ext i j
  rw [sigmaGL_apply, sigmaGL_apply, sigmaTensor_sigmaTensor K L A σ hσ]

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem coe_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (γ : Matrix (Fin 2) (Fin 2) A).map incl := rfl

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) : sG (ι γ) = ι γ := by
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_one_tmul]

theorem trace_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      incl (γ : Matrix (Fin 2) (Fin 2) A).trace := by
  rw [coe_toTensorGL, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.map_apply, map_add]

theorem det_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      incl (γ : Matrix (Fin 2) (Fin 2) A).det := by
  rw [coe_toTensorGL, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, map_sub, map_mul]

theorem trace_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      sT (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [coe_sigmaGL, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.map_apply, map_add]

theorem det_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      sT (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [coe_sigmaGL, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, map_sub, map_mul]

theorem isRegularSemisimple_toTensorGL (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (ι γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  rw [trace_toTensorGL, det_toTensorGL]
  have : incl (γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * incl (γ : Matrix (Fin 2) (Fin 2) A).det =
      incl ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [this]
  exact hγ.map _

theorem trace_units_conj' (x g : GL (Fin 2) (L ⊗[K] A)) :
    ((x⁻¹ * g * x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mul]

theorem det_units_conj' (x g : GL (Fin 2) (L ⊗[K] A)) :
    ((x⁻¹ * g * x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem normString_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ = δ * sG δ := by
  simp [AutomorphicForm.normString, h2, List.range_succ]

theorem mem_twistedCentralizer_iff (δ t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔ t * δ = δ * sG t := by
  rw [AutomorphicForm.twistedCentralizer, AutomorphicForm.mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]

variable (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
include h2 hσ

theorem sigmaGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sG (AutomorphicForm.normString K L A σ δ) = sG δ * δ := by
  rw [normString_two K L A σ h2, map_mul, sigmaGL_sigmaGL K L A σ hσ]

theorem normString_conj (δ x : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ (x⁻¹ * δ * sG x) =
      x⁻¹ * AutomorphicForm.normString K L A σ δ * x := by
  rw [normString_two K L A σ h2, normString_two K L A σ h2, map_mul, map_mul, map_inv,
    sigmaGL_sigmaGL K L A σ hσ]
  group

theorem sigmaTensor_trace_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sT ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [← trace_sigmaGL, sigmaGL_normString K L A σ h2 hσ, normString_two K L A σ h2, Units.val_mul,
    Units.val_mul, Matrix.trace_mul_comm]

theorem sigmaTensor_det_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sT ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [← det_sigmaGL, sigmaGL_normString K L A σ h2 hσ, normString_two K L A σ h2, Units.val_mul,
    Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm]

theorem twistedCentralizer_le_centralizer_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [mem_twistedCentralizer_iff] at ht
  rw [Subgroup.mem_centralizer_singleton_iff, normString_two K L A σ h2]
  have h1 : sG t * sG δ = sG δ * t := by
    have := congrArg sG ht
    rwa [map_mul, map_mul, sigmaGL_sigmaGL K L A σ hσ] at this
  symm
  calc δ * sG δ * t = δ * (sG δ * t) := by rw [mul_assoc]
    _ = δ * (sG t * sG δ) := by rw [h1]
    _ = (δ * sG t) * sG δ := by rw [mul_assoc]
    _ = t * δ * sG δ := by rw [← ht]
    _ = t * (δ * sG δ) := by rw [mul_assoc]

theorem mem_twistedCentralizer_conj_iff (δ x t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ (x⁻¹ * δ * sG x) ↔
      x * t * x⁻¹ ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  rw [mem_twistedCentralizer_iff, mem_twistedCentralizer_iff, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc x * t * x⁻¹ * δ = x * (t * (x⁻¹ * δ * sG x)) * (sG x)⁻¹ := by group
      _ = x * (x⁻¹ * δ * sG x * sG t) * (sG x)⁻¹ := by rw [h]
      _ = δ * (sG x * sG t * (sG x)⁻¹) := by group
  · intro h
    calc t * (x⁻¹ * δ * sG x) = x⁻¹ * (x * t * x⁻¹ * δ) * sG x := by group
      _ = x⁻¹ * (δ * (sG x * sG t * (sG x)⁻¹)) * sG x := by rw [h]
      _ = x⁻¹ * δ * sG x * sG t := by group

end Twist

section Injective

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem _root_.P2mFinUnits.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "P2mFinUnits" "includeRight_injective"

theorem toTensorGL_injective : Function.Injective (AutomorphicForm.toTensorGL K L A) := by
  intro g g' h
  apply Units.ext
  ext i j
  have := congrArg (fun m : GL (Fin 2) (L ⊗[K] A) => (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) h
  simp only [toTensorGL_apply] at this
  exact includeRight_injective K L A this

end Injective

section Galois

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]

theorem sigma_involutive_and_ne_one (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∃ ℓ : L, σ ℓ ≠ ℓ := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · by_contra h
    push Not at h
    have hσ1 : σ = 1 := AlgEquiv.ext h
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      rw [← hk, hσ1, one_zpow]
    have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

theorem exists_algebraMap_eq_of_fixed (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {l : L} (hl : σ l = l) :
    ∃ k : K, algebraMap K L k = l := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hzpow : ∀ k : ℤ, (σ ^ k) l = l := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hl, ih]
    | pred k ih =>
        have hinv : σ⁻¹ l = l := by
          rw [AlgEquiv.aut_inv]
          conv_lhs => rw [← hl]
          exact σ.symm_apply_apply l
        rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]
  have hfix : ∀ f : L ≃ₐ[K] L, f l = l := fun f => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen f)
    rw [← hk]
    exact hzpow k
  exact (IsGalois.mem_range_algebraMap_iff_fixed l).mpr hfix

variable (A : Type) [CommRing A] [Algebra K A]

theorem exists_one_tmul_of_sigmaTensor_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {b : L ⊗[K] A}
    (hb : AutomorphicForm.sigmaTensor K L A σ b = b) : ∃ a : A, b = (1 : L) ⊗ₜ[K] a := by

  have hsym : ∀ b : L ⊗[K] A, ∃ a : A, b + AutomorphicForm.sigmaTensor K L A σ b = (1 : L) ⊗ₜ[K] a := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l a =>
        obtain ⟨k, hk⟩ := exists_algebraMap_eq_of_fixed K L h2 σ hgen (l := l + σ l)
          (by rw [map_add, (sigma_involutive_and_ne_one K L h2 σ hgen).1 l, add_comm])
        refine ⟨k • a, ?_⟩
        rw [sigmaTensor_tmul, ← TensorProduct.add_tmul, ← hk, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨a', ha'⟩ := hy
        refine ⟨a + a', ?_⟩
        rw [map_add, TensorProduct.tmul_add, ← ha, ← ha']
        abel
  obtain ⟨a, ha⟩ := hsym b
  rw [hb, ← two_smul K b] at ha
  refine ⟨(2 : K)⁻¹ • a, ?_⟩
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', ← ha, smul_smul,
    inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0), one_smul]

theorem exists_toTensorGL_eq_of_sigmaGL_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {g : GL (Fin 2) (L ⊗[K] A)}
    (hg : AutomorphicForm.sigmaGL K L A σ g = g) : ∃ m : GL (Fin 2) A, AutomorphicForm.toTensorGL K L A m = g := by
  set incl : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight with hincl
  have hginv : AutomorphicForm.sigmaGL K L A σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  have hent : ∀ (u : GL (Fin 2) (L ⊗[K] A)), AutomorphicForm.sigmaGL K L A σ u = u →
      ∃ m : Matrix (Fin 2) (Fin 2) A, m.map incl = (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    intro u hu
    have hij : ∀ i j, ∃ a : A, (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = (1 : L) ⊗ₜ[K] a := by
      intro i j
      apply exists_one_tmul_of_sigmaTensor_eq K L A h2 σ hgen
      have := congrArg (fun m : GL (Fin 2) (L ⊗[K] A) => (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) hu
      simpa only [sigmaGL_apply] using this
    choose a ha using hij
    refine ⟨Matrix.of fun i j => a i j, ?_⟩
    ext i j
    rw [ha i j]
    rfl
  obtain ⟨m, hm⟩ := hent g hg
  obtain ⟨m', hm'⟩ := hent g⁻¹ hginv
  have hmapinj : Function.Injective fun x : Matrix (Fin 2) (Fin 2) A => x.map incl := by
    intro x y hxy
    ext i j
    exact includeRight_injective K L A (congrFun (congrFun hxy i) j)
  have hmm' : m * m' = 1 := by
    apply hmapinj
    change (m * m').map incl.toRingHom = (1 : Matrix (Fin 2) (Fin 2) A).map incl.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    change m.map incl * m'.map incl = 1
    rw [hm, hm', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm'm : m' * m = 1 := by
    apply hmapinj
    change (m' * m).map incl.toRingHom = (1 : Matrix (Fin 2) (Fin 2) A).map incl.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    change m'.map incl * m.map incl = 1
    rw [hm, hm', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨m, m', hmm', hm'm⟩, Units.ext ?_⟩
  exact hm

end Galois

section Torus

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "ι" => AutomorphicForm.toTensorGL K L A
local notation "Nm" => AutomorphicForm.normString K L A σ

theorem comm_of_mem_centralizer_toTensorGL {γ₁ : GL (Fin 2) A} (hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁)
    {a b : GL (Fin 2) (L ⊗[K] A)}
    (ha : a ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))))
    (hb : b ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A)))) : a * b = b * a :=
  mul_comm_of_mem_centralizer (isRegularSemisimple_toTensorGL K L A γ₁ hγ₁) ha hb

theorem toTensorGL_mem_centralizer_iff {γ₁ m : GL (Fin 2) A} :
    ι m ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) ↔
      m ∈ Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) A)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact ⟨fun h => toTensorGL_injective K L A h, fun h => by rw [h]⟩

theorem mem_twistedCentralizer_mul_self {δ u : GL (Fin 2) (L ⊗[K] A)}
    (hu : u ∈ AutomorphicForm.twistedCentralizer K L A σ δ) :
    u ∈ AutomorphicForm.twistedCentralizer K L A σ (u * δ) := by
  rw [mem_twistedCentralizer_iff] at hu ⊢
  rw [mul_assoc, ← hu]

theorem mem_twistedCentralizer_of_commute {δ u t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ AutomorphicForm.twistedCentralizer K L A σ (u * δ)) (hc : t * u = u * t) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  rw [mem_twistedCentralizer_iff] at ht ⊢
  rw [← mul_assoc, hc, mul_assoc, mul_assoc] at ht
  exact mul_left_cancel ht

include h2 hgen

theorem mem_centralizer_of_normString_eq {δ₀ : GL (Fin 2) (L ⊗[K] A)} {γ₁ : GL (Fin 2) A}
    (hN : Nm δ₀ = ι γ₁) : δ₀ ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  have h1 : sG δ₀ * δ₀ = δ₀ * sG δ₀ := by
    have := sigmaGL_normString K L A σ h2 hσ δ₀
    rw [hN, sigmaGL_toTensorGL, ← hN, normString_two K L A σ h2] at this
    exact this.symm
  rw [Subgroup.mem_centralizer_singleton_iff, ← hN, normString_two K L A σ h2]
  symm
  calc δ₀ * sG δ₀ * δ₀ = δ₀ * (sG δ₀ * δ₀) := by rw [mul_assoc]
    _ = δ₀ * (δ₀ * sG δ₀) := by rw [h1]

theorem mem_twistedCentralizer_iff_of_normString_eq {δ₀ : GL (Fin 2) (L ⊗[K] A)} {γ₁ : GL (Fin 2) A}
    (hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁) (hN : Nm δ₀ = ι γ₁) (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ₀ ↔
      ∃ m ∈ Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) A)), ι m = t := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  have hδ₀ := mem_centralizer_of_normString_eq K L A h2 σ hgen hN
  constructor
  · intro ht
    have htC : t ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) := by
      rw [← hN]
      exact twistedCentralizer_le_centralizer_normString K L A σ h2 hσ δ₀ ht
    rw [mem_twistedCentralizer_iff] at ht
    have hcomm : t * δ₀ = δ₀ * t := comm_of_mem_centralizer_toTensorGL K L A hγ₁ htC hδ₀
    have hfix : sG t = t := by
      rw [hcomm] at ht
      exact (mul_left_cancel ht).symm
    obtain ⟨m, hm⟩ := exists_toTensorGL_eq_of_sigmaGL_eq K L A h2 σ hgen hfix
    refine ⟨m, ?_, hm⟩
    rw [← toTensorGL_mem_centralizer_iff K L A, hm]
    exact htC
  · rintro ⟨m, hm, rfl⟩
    have htC : ι m ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) :=
      (toTensorGL_mem_centralizer_iff K L A).2 hm
    rw [mem_twistedCentralizer_iff, sigmaGL_toTensorGL]
    exact comm_of_mem_centralizer_toTensorGL K L A hγ₁ htC hδ₀

theorem mem_twistedCentralizer_iff_of_isNormConjugator {γ : GL (Fin 2) A}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) {δ₁ y : GL (Fin 2) (L ⊗[K] A)}
    (hy : AutomorphicForm.IsNormConjugator K L A σ γ δ₁ y) (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ₁ ↔
      ∃ m ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), y * ι m * y⁻¹ = t := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1

  have hN : Nm (y⁻¹ * δ₁ * sG y) = ι γ := by
    rw [normString_conj K L A σ h2 hσ]
    exact hy.symm
  have key := mem_twistedCentralizer_iff_of_normString_eq K L A h2 σ hgen hγ hN (y⁻¹ * t * y)
  have hconj : y⁻¹ * t * y ∈ AutomorphicForm.twistedCentralizer K L A σ (y⁻¹ * δ₁ * sG y) ↔
      t ∈ AutomorphicForm.twistedCentralizer K L A σ δ₁ := by
    rw [mem_twistedCentralizer_conj_iff K L A σ h2 hσ]
    have : y * (y⁻¹ * t * y) * y⁻¹ = t := by group
    rw [this]
  rw [← hconj, key]
  constructor
  · rintro ⟨m, hm, hmt⟩
    exact ⟨m, hm, by rw [hmt]; group⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, by group⟩

end Torus

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem continuous_toTensorGL : Continuous (AutomorphicForm.toTensorGL K L A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have hincl : Continuous
      ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom) := by
    have h := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (L ⊗[K] A))
    exact h
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map hincl

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

theorem exists_continuousMulEquiv [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    (P : Subgroup (GL (Fin 2) A)) (hP : IsClosed (P : Set (GL (Fin 2) A)))
    (Q : Subgroup (GL (Fin 2) (L ⊗[K] A))) (hQ : IsClosed (Q : Set (GL (Fin 2) (L ⊗[K] A))))
    (y : GL (Fin 2) (L ⊗[K] A))
    (hPQ : ∀ q, q ∈ Q ↔ ∃ p ∈ P, y * AutomorphicForm.toTensorGL K L A p * y⁻¹ = q) :
    ∃ e : P ≃ₜ* Q, ∀ p : P, ((e p : Q) : GL (Fin 2) (L ⊗[K] A)) = y * AutomorphicForm.toTensorGL K L A p * y⁻¹ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L A
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  haveI : SigmaCompactSpace (GL (Fin 2) A) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace P := hP.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set ι := AutomorphicForm.toTensorGL K L A with hιdef
  let f : P →* Q :=
    { toFun := fun p => ⟨y * ι p * y⁻¹, (hPQ _).2 ⟨p, p.2, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p p' => Subtype.ext (by
        change y * ι ((p : GL (Fin 2) A) * (p' : GL (Fin 2) A)) * y⁻¹ = y * ι p * y⁻¹ * (y * ι p' * y⁻¹)
        rw [map_mul]
        group) }
  have hfval : ∀ p : P, ((f p : Q) : GL (Fin 2) (L ⊗[K] A)) = y * ι p * y⁻¹ := fun p => rfl
  have hfc : Continuous f := by
    have : Continuous fun p : P => y * ι (p : GL (Fin 2) A) * y⁻¹ :=
      (continuous_const.mul ((continuous_toTensorGL K L A).comp continuous_subtype_val)).mul continuous_const
    exact this.subtype_mk _
  have hfinj : Function.Injective f := by
    intro p p' h
    have h' : y * ι p * y⁻¹ = y * ι p' * y⁻¹ := by
      rw [← hfval, ← hfval, h]
    have h'' : ι p = ι p' := by
      have := congrArg (fun g => y⁻¹ * g * y) h'
      simpa [mul_assoc] using this
    exact Subtype.ext (toTensorGL_injective K L A h'')
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨p, hp, hpq⟩ := (hPQ q).1 q.2
    exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩
  have hopen : IsOpenMap f := MonoidHom.isOpenMap_of_sigmaCompact f hfsurj hfc
  let e₀ : P ≃ Q := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  let h : P ≃ₜ Q := e₀.toHomeomorphOfContinuousOpen hfc hopen
  refine ⟨{ MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩ with
      continuous_toFun := hfc
      continuous_invFun := h.symm.continuous }, fun p => rfl⟩

end TensorTopology

section Retraction

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem exists_linearMap_map_one : ∃ f : L →ₗ[K] K, f 1 = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  refine ⟨g, ?_⟩
  have := congrArg (fun φ : K →ₗ[K] K => φ 1) hg
  simpa using this

theorem smul_tmul_right (x : A) (l : L) (a : A) : x • (l ⊗ₜ[K] a : L ⊗[K] A) = l ⊗ₜ[K] (x * a) := by
  simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
  rw [TensorProduct.smul_tmul']
  simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]

theorem exists_continuous_retraction :
    ∃ r : L ⊗[K] A → A, Continuous r ∧ ∀ a : A, r ((1 : L) ⊗ₜ[K] a) = a := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  obtain ⟨f, hf⟩ := exists_linearMap_map_one K L

  let B : L →ₗ[K] A →ₗ[K] A := (LinearMap.lsmul K A).comp f
  let r₀ : L ⊗[K] A →ₗ[K] A := TensorProduct.lift B
  have hr₀ : ∀ (l : L) (a : A), r₀ (l ⊗ₜ[K] a) = f l • a := fun l a => by
    simp [r₀, B, TensorProduct.lift.tmul]

  let rA : L ⊗[K] A →ₗ[A] A :=
    { toFun := r₀
      map_add' := fun x y => map_add r₀ x y
      map_smul' := fun x z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => simp
        | tmul l a =>
          rw [smul_tmul_right K L A, hr₀, hr₀]
          simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
          ring
        | add y y' hy hy' => simp only [smul_add, map_add, hy, hy'] }
  refine ⟨r₀, ?_, fun a => ?_⟩
  · exact (IsModuleTopology.continuous_of_linearMap rA : Continuous rA)
  · rw [hr₀, hf, one_smul]

end Retraction

section Units

open NumberField IsDedekindDomain AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "GE" => GL (Fin 2) (L ⊗[K] HeightOneSpectrum.adicCompletion K v)
local notation "incl" => (Algebra.TensorProduct.includeRight : HeightOneSpectrum.adicCompletion K v →ₐ[K] L ⊗[K] HeightOneSpectrum.adicCompletion K v)

theorem exists_det_eq_map (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ t : GE) (ht : t ∈ twistedCentralizer K L F σ δ) :
    ∃ s : Fˣ, Matrix.GeneralLinearGroup.det t = Units.map (incl).toRingHom.toMonoidHom s := by

  have h1 : t * δ * (sigmaGL K L F σ t)⁻¹ = δ := mem_sigmaCentralizer_iff.mp ht
  have h2' : Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det (sigmaGL K L F σ t) := by
    have := congrArg Matrix.GeneralLinearGroup.det h1
    rw [map_mul, map_mul, map_inv] at this

    have h3 := mul_inv_eq_iff_eq_mul.mp this
    rw [mul_comm (Matrix.GeneralLinearGroup.det δ)] at h3
    exact mul_right_cancel h3
  have hfix : sigmaTensor K L F σ ((t : Matrix (Fin 2) (Fin 2) E).det) = (t : Matrix (Fin 2) (Fin 2) E).det := by
    have := congrArg (fun u : (E)ˣ => (u : E)) h2'
    simp only [Matrix.GeneralLinearGroup.val_det_apply] at this
    rw [det_sigmaGL] at this
    exact this.symm
  obtain ⟨a, ha⟩ := exists_one_tmul_of_sigmaTensor_eq K L F h2 σ hgen hfix
  have ha0 : a ≠ 0 := by
    intro h0
    have hu : IsUnit ((t : Matrix (Fin 2) (Fin 2) E).det) := (Matrix.isUnit_iff_isUnit_det _).mp t.isUnit
    rw [ha, h0, TensorProduct.tmul_zero] at hu
    haveI : Nontrivial E := ⟨⟨(1 : L) ⊗ₜ[K] (0 : F), (1 : L) ⊗ₜ[K] (1 : F), fun h =>
      zero_ne_one ((includeRight_injective K L F) h)⟩⟩
    exact not_isUnit_zero hu
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.coe_coe,
    Units.val_mk0]
  exact ha

end Units

section Main

open NumberField IsDedekindDomain AutomorphicForm

theorem continuous_glScalar (F₀ : Type) [CommRing F₀] [TopologicalSpace F₀] [IsTopologicalRing F₀] :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) : F₀ˣ → GL (Fin 2) F₀) := by
  unfold Matrix.GeneralLinearGroup.scalar
  refine Continuous.units_map _ ?_
  show Continuous fun a : F₀ => Matrix.scalar (Fin 2) a
  simp_rw [Matrix.scalar_apply]
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

theorem det_coe_glScalar (F₀ : Type) [CommRing F₀] (e : F₀ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) e : GL (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀).det = (e : F₀) ^ 2 := by
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) e : GL (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) =
      Matrix.diagonal fun _ => (e : F₀) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]
  rw [h, Matrix.det_diagonal, Fin.prod_univ_two, pow_two]

end Main
end P2mFinUnits

namespace P2mFinWeil

open NumberField IsDedekindDomain AutomorphicForm P2mFinUnits

set_option maxHeartbeats 16000000 in
theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy₁ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₁)
    (hS : ∀ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
        ∃ m ∈ AutomorphicForm.localCentralizer K v γ₀,
          y₁ * AutomorphicForm.toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = t)
    (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT)
    (hlink : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
           AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
       Measure.map (fun s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
           y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) τS =
         Measure.map (fun m : ↥(AutomorphicForm.localCentralizer K v γ₀) =>
           AutomorphicForm.toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) τT))
    (hdetK : ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Matrix.GeneralLinearGroup.det t =
        Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s)
    (hUo : IsOpen {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (hUc : IsCompact {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (hϖ : ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t =
          Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s)
    (htr : ∀ m ∈ AutomorphicForm.localCentralizer K v γ₀, Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 →
      Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1) :
      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
       ∀ ρ : ℝ,
        (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
               AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
           (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
             ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
               ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                   AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
                 w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                   ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           ∫ t, w t ∂τ' = ρ)) →
        ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal) ∧
        ((¬ (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ))) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = 2 * (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal)) := by
  classical

  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf _
  letI mF : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  letI mT' : MeasurableSpace ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  letI mS : MeasurableSpace ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
      twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
  haveI : BorelSpace ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
      twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := ⟨rfl⟩
  letI mT : MeasurableSpace ↥(localCentralizer K v γ₀) := localCentralizerBorel K v γ₀
  haveI : BorelSpace ↥(localCentralizer K v γ₀) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ' := hτ'
  haveI : Measure.IsHaarMeasure τS := hτS
  haveI : Measure.IsHaarMeasure τT := hτT

  obtain ⟨r, hrc, hr1⟩ := exists_continuous_retraction K L (v.adicCompletion K)
  have hdval : ∀ (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (s : (v.adicCompletion K)ˣ),
      Matrix.GeneralLinearGroup.det t =
        Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s →
      r ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det) = (s : v.adicCompletion K) := by
    intro t s h
    have h' := congrArg (fun u : (L ⊗[K] v.adicCompletion K)ˣ => (u : L ⊗[K] v.adicCompletion K)) h
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe] at h'
    rw [h']
    exact hr1 s
  set ν : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → WithZero (Multiplicative ℤ) :=
    fun g => Valued.v (r ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det)) with hν

  have hνT : ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ s : (v.adicCompletion K)ˣ,
      Matrix.GeneralLinearGroup.det t =
        Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s ∧
      ν t = Valued.v (s : v.adicCompletion K) := by
    intro t ht
    obtain ⟨s, hs⟩ := hdetK t ht
    exact ⟨s, hs, by simp only [hν]; rw [hdval t s hs]⟩
  have hν0 : ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ, ν t ≠ 0 := by
    intro t ht
    obtain ⟨s, -, hs⟩ := hνT t ht
    rw [hs]; exact (Valuation.ne_zero_iff _).mpr s.ne_zero
  have hνmul : ∀ t₁ ∈ twistedCentralizer K L (v.adicCompletion K) σ δ, ∀ t₂ ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
      ν (t₁ * t₂) = ν t₁ * ν t₂ := by
    intro t₁ h₁ t₂ h₂
    obtain ⟨s₁, hs₁, hν₁⟩ := hνT t₁ h₁
    obtain ⟨s₂, hs₂, hν₂⟩ := hνT t₂ h₂
    have h12 : Matrix.GeneralLinearGroup.det (t₁ * t₂) =
        Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom (s₁ * s₂) := by
      rw [map_mul, map_mul, hs₁, hs₂]
    simp only [hν] at hν₁ hν₂ ⊢
    rw [hdval _ _ h12, hν₁, hν₂, Units.val_mul, map_mul]
  have hν1 : ν 1 = 1 := by
    simp only [hν, Units.val_one, Matrix.det_one]
    rw [show (1 : L ⊗[K] v.adicCompletion K) = (1 : L) ⊗ₜ[K] (1 : v.adicCompletion K) from rfl, hr1, map_one]
  have hνinv : ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ, ν t⁻¹ = (ν t)⁻¹ := by
    intro t ht
    have h := hνmul t⁻¹ (inv_mem ht) t ht
    rw [inv_mul_cancel, hν1] at h
    exact (eq_inv_of_mul_eq_one_left h.symm)

  set U : Set ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} with hUdef
  have hmemU : ∀ t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ), t ∈ U ↔ ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = 1 := by
    intro t
    constructor
    · rintro ⟨s, hs, h⟩
      simp only [hν]; rw [hdval _ _ h]; exact hs
    · intro h
      obtain ⟨s, hs, hνs⟩ := hνT t t.2
      exact ⟨s, by rw [← hνs]; exact h, hs⟩

  set j : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) →
      ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    fun s => ⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ with hj
  have hjc : Continuous j := continuous_subtype_val.subtype_mk _
  have hjm : Measurable j := hjc.measurable
  have hSmem : ∀ s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
      (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ twistedCentralizer K L (v.adicCompletion K) σ δ :=
    fun s => (Subgroup.mem_inf.mp s.2).1

  have hνconj : ∀ m : GL (Fin 2) (v.adicCompletion K),
      ν (y₁ * toTensorGL K L (v.adicCompletion K) m * y₁⁻¹) =
        Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) := by
    intro m
    simp only [hν]
    have : ((y₁ * toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det =
        ((toTensorGL K L (v.adicCompletion K) m : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det := by
      rw [show y₁ * toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = (y₁⁻¹)⁻¹ * toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ by
        rw [inv_inv], det_units_conj']
    rw [this, det_toTensorGL]
    exact congrArg _ (hr1 _)

  set SU : Set ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) :=
    j ⁻¹' U with hSU
  have hmemSU : ∀ s, s ∈ SU ↔ ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = 1 := by
    intro s; rw [hSU, Set.mem_preimage, hmemU]
  have hSUo : IsOpen SU := hUo.preimage hjc
  have hSUm : MeasurableSet SU := hSUo.measurableSet
  have hSUc : IsCompact SU := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have hcl : IsClosed ((twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) :
        Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
      rw [Subgroup.coe_inf]
      exact (isClosed_twistedCentralizer K L (v.adicCompletion K) σ δ).inter
        (isClosed_twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ))
    have hval : Subtype.val '' SU = (Subtype.val '' U) ∩
        ((twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) :
          Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
      ext g
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨j s, hs, rfl⟩, s.2⟩
      · rintro ⟨⟨t, ht, htg⟩, hg⟩
        refine ⟨⟨g, hg⟩, ?_, rfl⟩
        show j ⟨g, hg⟩ ∈ U
        have : j ⟨g, hg⟩ = t := Subtype.ext htg.symm
        rw [this]; exact ht
    rw [hval]
    exact (hUc.image continuous_subtype_val).inter_right hcl
  have h1SU : (1 : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ))) ∈ SU := by
    rw [hmemSU]; exact hν1
  have hm₀pos : 0 < τS SU := hSUo.measure_pos τS ⟨1, h1SU⟩
  have hm₀fin : τS SU < ⊤ := hSUc.measure_lt_top
  set m₀ : ℝ := (τS SU).toReal with hm₀
  have hm₀r : 0 < m₀ := ENNReal.toReal_pos hm₀pos.ne' hm₀fin.ne

  have hshell : ∀ s₀ : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
      {s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) |
          ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = ν (s₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))} =
        (fun s => s₀⁻¹ * s) ⁻¹' SU := by
    intro s₀
    ext s
    rw [Set.mem_setOf_eq, Set.mem_preimage, hmemSU, Subgroup.coe_mul, Subgroup.coe_inv,
      hνmul _ (inv_mem (hSmem s₀)) _ (hSmem s), hνinv _ (hSmem s₀)]
    rw [inv_mul_eq_one₀ (hν0 _ (hSmem s₀))]
    exact comm
  have hshell_meas : ∀ s₀ : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
      τS {s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) |
          ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = ν (s₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))} = τS SU := by
    intro s₀; rw [hshell s₀, measure_preimage_mul]

  have hSν : ∀ s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
      ∃ m ∈ localCentralizer K v γ₀, ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
        Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) := by
    intro s
    obtain ⟨m, hm, hms⟩ := (hS s).mp s.2
    exact ⟨m, hm, by rw [← hms, hνconj]⟩
  have hTS : ∀ m ∈ localCentralizer K v γ₀, ∃ s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
      ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) := by
    intro m hm
    refine ⟨⟨y₁ * toTensorGL K L (v.adicCompletion K) m * y₁⁻¹, (hS _).mpr ⟨m, hm, rfl⟩⟩, ?_⟩
    exact hνconj m

  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  have hπv : Valued.v ((π : K) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h; rw [h, map_zero] at hπv; exact WithZero.exp_ne_zero hπv.symm
  set πu : (v.adicCompletion K)ˣ := Units.mk0 _ hπ0 with hπu
  have hscal_mem : ∀ k : ℤ, Matrix.GeneralLinearGroup.scalar (Fin 2) (πu ^ k) ∈ localCentralizer K v γ₀ := by
    intro k
    show Matrix.GeneralLinearGroup.scalar (Fin 2) (πu ^ k) ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) (v.adicCompletion K)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute ((πu ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) (fun r' => (mul_comm _ r'))
      (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).eq
  have hscal_v : ∀ k : ℤ, Valued.v (((Matrix.GeneralLinearGroup.scalar (Fin 2) (πu ^ k) : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det = WithZero.exp (-(2 * k)) := by
    intro k
    rw [det_coe_glScalar, map_pow, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hπv,
      ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]
    congr 1; simp only [smul_eq_mul, nsmul_eq_mul]; push_cast; ring
  have hdet_zpow : ∀ (m : GL (Fin 2) (v.adicCompletion K)) (k : ℤ),
      Valued.v (((m ^ k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det =
        Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) ^ k := by
    intro m k
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply, map_zpow,
      Units.val_zpow_eq_zpow_val, map_zpow₀]

  have hattA : (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
      ∀ n : ℤ, ∃ s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
        ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = WithZero.exp n := by
    rintro ⟨m, hm, hvm⟩ n
    obtain ⟨s, hs⟩ := hTS (m ^ (-n)) (Subgroup.zpow_mem _ hm _)
    refine ⟨s, ?_⟩
    rw [hs, hdet_zpow, hvm, show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) from rfl, ← WithZero.exp_zsmul]
    congr 1; simp

  have hattB : ¬ (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
      (∀ s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
          ∃ jj : ℤ, ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = WithZero.exp (2 * jj)) ∧
      (∀ jj : ℤ, ∃ s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
          ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = WithZero.exp (2 * jj)) := by
    intro hn
    constructor
    · intro s
      obtain ⟨m, hm, hνs⟩ := hSν s
      have hne : Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) ≠ 0 := by
        rw [← hνs]; exact hν0 _ (hSmem s)
      have ha : Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) =
          WithZero.exp (WithZero.log (Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det))) :=
        (WithZero.exp_log hne).symm
      obtain ⟨jj, hjj | hjj⟩ := Int.even_or_odd' (WithZero.log (Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det)))
      · exact ⟨jj, by rw [hνs, ha, hjj]⟩
      · exfalso
        apply hn
        refine ⟨m * Matrix.GeneralLinearGroup.scalar (Fin 2) (πu ^ (jj + 1)), mul_mem hm (hscal_mem _), ?_⟩
        rw [Units.val_mul, Matrix.det_mul, map_mul, ha, hscal_v, hjj, ← WithZero.exp_add,
          show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) from rfl]
        congr 1; ring
    · intro jj
      obtain ⟨s, hs⟩ := hTS _ (hscal_mem (-jj))
      exact ⟨s, by rw [hs, hscal_v]; congr 1; ring⟩

  obtain ⟨ϖD, hϖDmem, sϖ, hsϖ, hdetϖ⟩ := hϖ
  have hνϖ : ν ϖD = WithZero.exp (-1 : ℤ) := by simp only [hν]; rw [hdval _ _ hdetϖ, hsϖ]
  set ϖD' : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨ϖD, hϖDmem⟩ with hϖD'
  set U' : Set ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    {t | ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = WithZero.exp (-1 : ℤ)} with hU'def
  have hU'eq : U' = (fun t => ϖD'⁻¹ * t) ⁻¹' U := by
    ext t
    rw [Set.mem_preimage, hmemU, hU'def, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv,
      hνmul _ (inv_mem hϖDmem) _ t.2, hνinv _ hϖDmem, hνϖ, inv_mul_eq_one₀ WithZero.exp_ne_zero]
    exact comm
  have hU'o : IsOpen U' := by rw [hU'eq]; exact hUo.preimage (continuous_const.mul continuous_id)
  have hU'c : IsCompact U' := by
    rw [hU'eq, show (fun t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) => ϖD'⁻¹ * t) = ⇑(Homeomorph.mulLeft ϖD'⁻¹) from rfl]
    exact (Homeomorph.mulLeft ϖD'⁻¹).isCompact_preimage.mpr hUc
  have hUm : MeasurableSet U := hUo.measurableSet
  have hU'm : MeasurableSet U' := hU'o.measurableSet
  have hτU' : τ' U' = τ' U := by rw [hU'eq, measure_preimage_mul]
  have hdisj : Disjoint U U' := by
    rw [Set.disjoint_left]
    intro t ht ht'
    rw [hmemU] at ht
    rw [hU'def, Set.mem_setOf_eq, ht] at ht'
    exact absurd (WithZero.exp_inj.mp (ht'.symm.trans WithZero.exp_zero.symm)) (by norm_num)
  have hUfin : τ' U < ⊤ := hUc.measure_lt_top

  have hfibU : ∀ t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ),
      (fun s => j s * t) ⁻¹' U =
        {s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) |
          ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = (ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)))⁻¹} := by
    intro t; ext s
    rw [Set.mem_preimage, hmemU, Set.mem_setOf_eq, Subgroup.coe_mul]
    show ν ((s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K))) = 1 ↔ _
    rw [hνmul _ (hSmem s) _ t.2, mul_eq_one_iff_eq_inv₀ (hν0 _ t.2)]
  have hfibU' : ∀ t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ),
      (fun s => j s * t) ⁻¹' U' =
        {s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) |
          ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = WithZero.exp (-1 : ℤ) * (ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)))⁻¹} := by
    intro t; ext s
    rw [Set.mem_preimage, hU'def, Set.mem_setOf_eq, Set.mem_setOf_eq, Subgroup.coe_mul]
    show ν ((s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K))) = _ ↔ _
    rw [hνmul _ (hSmem s) _ t.2, eq_mul_inv_iff_mul_eq₀ (hν0 _ t.2)]

  have hshell_att : ∀ γ : WithZero (Multiplicative ℤ),
      (∃ s₀ : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
          ν (s₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = γ) →
      τS {s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) |
          ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = γ} = τS SU := by
    rintro γ ⟨s₀, hs₀⟩
    rw [← hs₀]; exact hshell_meas s₀
  have hshell_empty : ∀ γ : WithZero (Multiplicative ℤ),
      (¬ ∃ s₀ : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
          ν (s₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = γ) →
      {s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) |
          ν (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = γ} = ∅ := by
    intro γ h
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hs => h ⟨s, hs⟩

  have hsection : ∀ (W : Set ↥(twistedCentralizer K L (v.adicCompletion K) σ δ)), IsOpen W → IsCompact W →
      (∀ t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ), τS ((fun s => j s * t) ⁻¹' W) = τS SU) →
      (∀ t, 0 ≤ W.indicator (fun _ => m₀⁻¹) t) ∧ Measurable (W.indicator (fun _ => m₀⁻¹)) ∧
        HasCompactSupport (W.indicator (fun _ => m₀⁻¹)) ∧
        (∀ t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ),
          ∫ s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
            W.indicator (fun _ => m₀⁻¹) (j s * t) ∂τS = 1) ∧
        ∫ t, W.indicator (fun _ => m₀⁻¹) t ∂τ' = (τ' W).toReal * m₀⁻¹ := by
    intro W hWo hWc hWfib
    have hWm : MeasurableSet W := hWo.measurableSet
    refine ⟨fun t => Set.indicator_nonneg (fun _ _ => inv_nonneg.2 hm₀r.le) t, measurable_const.indicator hWm,
      HasCompactSupport.intro hWc (fun t ht => Set.indicator_of_notMem ht _), fun t => ?_, ?_⟩
    · have hmeas : Measurable (fun s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) => j s * t) := (hjc.mul continuous_const).measurable
      have hfun : (fun s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
          W.indicator (fun _ => m₀⁻¹) (j s * t)) = ((fun s => j s * t) ⁻¹' W).indicator (fun _ => m₀⁻¹) := by
        funext s; simp only [Set.indicator_apply, Set.mem_preimage]
      rw [hfun, integral_indicator_const _ (hWm.preimage hmeas), measureReal_def, hWfib t, smul_eq_mul, ← hm₀,
        mul_inv_cancel₀ hm₀r.ne']
    · rw [integral_indicator_const _ hWm, measureReal_def, smul_eq_mul]

  have hn1 : ∀ x : v.adicCompletion K, ‖x‖ = 1 ↔ Valued.v x = 1 := by
    intro x
    constructor
    · intro h
      exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mp h.le) (Valued.toNormedField.one_le_norm_iff.mp h.ge)
    · intro h
      exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr h.le) (Valued.toNormedField.one_le_norm_iff.mpr h.ge)
  have hle1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  set B₀ : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    {g | ‖r ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det)‖ = 1} with hB₀
  have hB₀c : IsClosed B₀ := isClosed_eq ((hrc.comp Units.continuous_val.matrix_det).norm) continuous_const
  have hB₀m : MeasurableSet B₀ := hB₀c.measurableSet
  have hfS : Measurable (fun s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
      y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hfT : Measurable (fun m : ↥(localCentralizer K v γ₀) => toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) :=
    ((continuous_toTensorGL K L (v.adicCompletion K)).comp continuous_subtype_val).measurable
  have hlinkB := congrArg (fun μ : Measure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) => μ B₀) hlink
  rw [Measure.map_apply hfS hB₀m, Measure.map_apply hfT hB₀m] at hlinkB
  have hpreS : (fun s : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
      y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) ⁻¹' B₀ = SU := by
    ext s
    rw [Set.mem_preimage, hB₀, Set.mem_setOf_eq, det_units_conj', hn1, hmemSU]
  set TU : Set ↥(localCentralizer K v γ₀) :=
    {m | Valued.v (((m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1} with hTU
  have hpreT : (fun m : ↥(localCentralizer K v γ₀) => toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) ⁻¹' B₀ = TU := by
    ext m
    rw [Set.mem_preimage, hB₀, Set.mem_setOf_eq, det_toTensorGL, hTU, Set.mem_setOf_eq]
    have hrr : r (Algebra.TensorProduct.includeRight (((m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det)) =
        ((m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := hr1 _
    rw [hrr]
    exact hn1 _
  rw [hpreS, hpreT] at hlinkB

  have hTc_meas : MeasurableSet {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀ ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} := by
    haveI := t2Space_GL (v.adicCompletion K)
    have h1 : IsClosed {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀} := by
      show IsClosed ((localCentralizer K v γ₀ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K)))
      show IsClosed (({γ₀} : Set (GL (Fin 2) (v.adicCompletion K))).centralizer)
      exact Set.isClosed_centralizer _
    have h2' : IsClosed {g : GL (Fin 2) (v.adicCompletion K) | Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1} := by
      have : {g : GL (Fin 2) (v.adicCompletion K) | Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1} =
          {g : GL (Fin 2) (v.adicCompletion K) | ‖((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det‖ = 1} := by ext g; exact (hn1 _).symm
      rw [this]; exact isClosed_eq (Units.continuous_val.matrix_det.norm) continuous_const
    have h3 : IsClosed {g : GL (Fin 2) (v.adicCompletion K) | Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} := by
      have : {g : GL (Fin 2) (v.adicCompletion K) | Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} =
          {g : GL (Fin 2) (v.adicCompletion K) | ‖((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).trace‖ ≤ 1} := by ext g; exact (hle1 _).symm
      rw [this]; exact isClosed_le (Units.continuous_val.matrix_trace.norm) continuous_const
    rw [Set.setOf_and, Set.setOf_and]
    exact (h1.inter (h2'.inter h3)).measurableSet
  have hθ : ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀ ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = m₀ := by
    rw [Measure.map_apply (continuous_subtype_val.measurable) hTc_meas]
    have : (Subtype.val : ↥(localCentralizer K v γ₀) → GL (Fin 2) (v.adicCompletion K)) ⁻¹'
        {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} = TU := by
      ext m
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hTU]
      exact ⟨fun h => h.2.1, fun h => ⟨m.2, h, htr _ m.2 h⟩⟩
    rw [this, ← hlinkB, hm₀]

  intro ρ hρ
  refine ⟨fun hRam => ?_, fun hnRam => ?_⟩
  ·
    have hfib : ∀ t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ), τS ((fun s => j s * t) ⁻¹' U) = τS SU := by
      intro t
      rw [hfibU t]
      apply hshell_att
      have hne : (ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)))⁻¹ ≠ 0 := inv_ne_zero (hν0 _ t.2)
      obtain ⟨s, hs⟩ := hattA hRam (WithZero.log ((ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)))⁻¹))
      exact ⟨s, by rw [hs, WithZero.exp_log hne]⟩
    obtain ⟨h0, hme, hsu, hfi, hint⟩ := hsection U hUo hUc hfib
    have hρ' := hρ _ ⟨h0, hme, hsu, hfi⟩
    rw [hint] at hρ'
    rw [← hρ', hθ, mul_assoc, inv_mul_cancel₀ hm₀r.ne', mul_one]
  ·
    obtain ⟨hevS, hattS⟩ := hattB hnRam
    have hfib : ∀ t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ), τS ((fun s => j s * t) ⁻¹' (U ∪ U')) = τS SU := by
      intro t
      rw [Set.preimage_union, hfibU t, hfibU' t]
      have hνt : ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ≠ 0 := hν0 _ t.2
      set a : ℤ := WithZero.log (ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K))) with ha
      have hta : ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = WithZero.exp a := (WithZero.exp_log hνt).symm
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' a
      ·
        rw [hshell_empty (WithZero.exp (-1 : ℤ) * (ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)))⁻¹) ?_, Set.union_empty]
        · apply hshell_att
          obtain ⟨s, hs⟩ := hattS (-k)
          exact ⟨s, by rw [hs, hta, hk, ← WithZero.exp_neg]; congr 1; ring⟩
        · rintro ⟨s₀, hs₀⟩
          obtain ⟨jj, hjj⟩ := hevS s₀
          rw [hjj, hta, hk, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj] at hs₀
          omega
      ·
        rw [hshell_empty ((ν (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)))⁻¹) ?_, Set.empty_union]
        · apply hshell_att
          obtain ⟨s, hs⟩ := hattS (-k - 1)
          exact ⟨s, by rw [hs, hta, hk, ← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring⟩
        · rintro ⟨s₀, hs₀⟩
          obtain ⟨jj, hjj⟩ := hevS s₀
          rw [hjj, hta, hk, ← WithZero.exp_neg, WithZero.exp_inj] at hs₀
          omega
    obtain ⟨h0, hme, hsu, hfi, hint⟩ := hsection (U ∪ U') (hUo.union hU'o) (hUc.union hU'c) hfib
    have hρ' := hρ _ ⟨h0, hme, hsu, hfi⟩
    rw [hint, measure_union hdisj hU'm, hτU', ← two_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hρ'
    rw [← hρ', hθ, mul_assoc, inv_mul_cancel₀ hm₀r.ne', mul_one]

end P2mFinWeil

open MeasureTheory NumberField IsDedekindDomain in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy₁ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₁)
    (hS : ∀ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
        ∃ m ∈ AutomorphicForm.localCentralizer K v γ₀,
          y₁ * AutomorphicForm.toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = t)
    (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT)
    (hlink : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
           AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
       Measure.map (fun s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
           y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) τS =
         Measure.map (fun m : ↥(AutomorphicForm.localCentralizer K v γ₀) =>
           AutomorphicForm.toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) τT))
    (hdetK : ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Matrix.GeneralLinearGroup.det t =
        Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s)
    (hUo : IsOpen {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (hUc : IsCompact {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (hϖ : ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t =
          Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s)
    (htr : ∀ m ∈ AutomorphicForm.localCentralizer K v γ₀, Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 →
      Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1) :
      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
       ∀ ρ : ℝ,
        (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
               AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
           (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
             ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
               ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                   AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
                 w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                   ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           ∫ t, w t ∂τ' = ρ)) →
        ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal) ∧
        ((¬ (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ))) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = 2 * (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal)) :=
  P2mFinWeil.main K L h2 σ hgen v c δ hδ hδq τ' hτ' u₀ hu₀ γ₀ hγ₀ hγ₀e y₁ hy₁ hS τS hτS τT hτT hlink hdetK hUo hUc hϖ htr

end
end S_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator
end P2MW
export P2MW.S_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator (solution)
