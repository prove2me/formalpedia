-- Prove2me | solution 1 for AutomorphicForm.zero_mem_and_one_mem_and_add_mem_and_neg_mem_and_mul_mem_and_smul_mem_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/046b8993-8174-5339-84b7-6d37378c80fe

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Theorems.Thm_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_zero_mem_and_one_mem_and_add_mem_and_neg_mem_and_mul_mem_and_smul_mem_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain TopologicalSpace Topology Filter Set
open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Pointwise Matrix ENNReal NNReal

noncomputable section

namespace Ws31
namespace UltraNrd

open Matrix

theorem sq_eq_trace_smul_sub_det {R : Type} [CommRing R] (Z : Matrix (Fin 2) (Fin 2) R) :
    Z * Z = Z.trace • Z - Z.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.one_apply] <;> ring

theorem trace_pow_add_two {R : Type} [CommRing R] (Z : Matrix (Fin 2) (Fin 2) R) (m : ℕ) :
    (Z ^ (m + 2)).trace = Z.trace * (Z ^ (m + 1)).trace - Z.det * (Z ^ m).trace := by
  have h : Z ^ (m + 2) = Z.trace • Z ^ (m + 1) - Z.det • Z ^ m := by
    rw [pow_succ, pow_succ, mul_assoc, sq_eq_trace_smul_sub_det, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one,
      ← pow_succ]
  rw [h, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

theorem norm_newton_eq_pow {F : Type} [NormedField F] [IsUltrametricDist F]
    (t n : F) (ht : 1 < ‖t‖) (hn : ‖n‖ ≤ 1) (s : ℕ → F)
    (h0 : ‖s 0‖ ≤ 1) (h1 : s 1 = t) (hrec : ∀ m, s (m + 2) = t * s (m + 1) - n * s m) :
    ∀ m, ‖s (m + 1)‖ = ‖t‖ ^ (m + 1) := by

  have key : ∀ m, ‖s m‖ ≤ ‖t‖ ^ m ∧ ‖s (m + 1)‖ = ‖t‖ ^ (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using h0, by rw [h1, pow_one]⟩
    | succ m ih =>
      obtain ⟨hle, heq⟩ := ih
      refine ⟨heq.le, ?_⟩
      rw [hrec m]
      have hbig : ‖t * s (m + 1)‖ = ‖t‖ ^ (m + 2) := by
        rw [norm_mul, heq]; ring
      have hsmall : ‖n * s m‖ < ‖t * s (m + 1)‖ := by
        rw [hbig, norm_mul]
        calc ‖n‖ * ‖s m‖ ≤ 1 * ‖t‖ ^ m := by gcongr
          _ = ‖t‖ ^ m := one_mul _
          _ < ‖t‖ ^ (m + 2) := pow_lt_pow_right₀ ht (by omega)
      have hsmall' : ‖-(n * s m)‖ < ‖t * s (m + 1)‖ := by rwa [norm_neg]
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hsmall'), max_eq_left hsmall'.le, hbig]
  exact fun m => (key m).2

theorem not_bddAbove_newton {F : Type} [NormedField F] [IsUltrametricDist F]
    (t n : F) (ht : 1 < ‖t‖) (hn : ‖n‖ ≤ 1) (s : ℕ → F)
    (h0 : ‖s 0‖ ≤ 1) (h1 : s 1 = t) (hrec : ∀ m, s (m + 2) = t * s (m + 1) - n * s m)
    (B : ℝ) (hB : ∀ m, ‖s m‖ ≤ B) : False := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt B ht
  have := norm_newton_eq_pow t n ht hn s h0 h1 hrec m
  have h := hB (m + 1)
  rw [this] at h
  exact absurd (lt_of_lt_of_le hm (le_trans (pow_le_pow_right₀ ht.le (Nat.le_succ m)) h)) (lt_irrefl _)

section Algebra

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_algebraMap (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (algebraMap A (L ⊗[K] A) a) = algebraMap A (L ⊗[K] A) a := by
  change AutomorphicForm.sigmaTensor K L A σ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
  rw [sigmaTensor_tmul, map_one]

theorem sigmaTensor_sigmaTensor (hσ : ∀ l : L, σ (σ l) = l) (b : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A σ (AutomorphicForm.sigmaTensor K L A σ b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigma_facts (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∀ l : L, ∃ k : K, l + σ l = algebraMap K L k := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, fun l => ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · set m := l + σ l with hm
    have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have hσσ : σ (σ l) = l := by
      have := AlgEquiv.congr_fun hpow l
      rwa [pow_two, AlgEquiv.mul_apply] at this
    have hσm : σ m = m := by rw [hm, map_add, hσσ, add_comm]
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) m :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, hσm])
    have hfix : ∀ τ : L ≃ₐ[K] L, τ m = m := fun τ => by
      have := hle (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have hmem : m ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr fun τ _ => hfix τ
    rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk.symm⟩

theorem exists_add_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (e : L ⊗[K] A) :
    ∃ r : A, e + AutomorphicForm.sigmaTensor K L A σ e = algebraMap A (L ⊗[K] A) r := by
  obtain ⟨-, htr⟩ := sigma_facts K L σ h2 hgen
  induction e using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l a =>
      obtain ⟨k, hk⟩ := htr l
      refine ⟨k • a, ?_⟩
      rw [sigmaTensor_tmul, ← TensorProduct.add_tmul, hk, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      change (1 : L) ⊗ₜ[K] (k • a) = (k • a) • ((1 : L) ⊗ₜ[K] (1 : A))
      rw [TensorProduct.RightActions.smul_def]
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      obtain ⟨r₁, h₁⟩ := hx
      obtain ⟨r₂, h₂⟩ := hy
      refine ⟨r₁ + r₂, ?_⟩
      rw [map_add, map_add, ← h₁, ← h₂]
      abel

theorem exists_eq_algebraMap_of_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {e : L ⊗[K] A}
    (he : AutomorphicForm.sigmaTensor K L A σ e = e) :
    ∃ r : A, e = algebraMap A (L ⊗[K] A) r := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  obtain ⟨r, hr⟩ := exists_add_sigmaTensor_eq K L A σ h2 hgen e
  rw [he] at hr
  refine ⟨2⁻¹ * r, ?_⟩
  rw [map_mul, ← hr]
  have h2A : algebraMap A (L ⊗[K] A) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap A (L ⊗[K] A)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc e = (algebraMap A (L ⊗[K] A) 2⁻¹ * 2) * e := by rw [h2A, one_mul]
    _ = algebraMap A (L ⊗[K] A) 2⁻¹ * (e + e) := by rw [mul_assoc, two_mul]

theorem exists_leftInverse :
    ∃ pr : (L ⊗[K] A) →ₗ[A] A, ∀ a : A, pr (algebraMap A (L ⊗[K] A) a) = a := by
  have hinj : Function.Injective (algebraMap A (L ⊗[K] A)) := (algebraMap A (L ⊗[K] A)).injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap A (L ⊗[K] A))
    (LinearMap.ker_eq_bot.mpr hinj)
  exact ⟨g, fun a => by simpa using LinearMap.congr_fun hg a⟩

def pr : (L ⊗[K] A) →ₗ[A] A := Classical.choose (exists_leftInverse K L A)

theorem pr_algebraMap (a : A) : pr K L A (algebraMap A (L ⊗[K] A) a) = a :=
  Classical.choose_spec (exists_leftInverse K L A) a

def nrm (e : L ⊗[K] A) : A := pr K L A (e * AutomorphicForm.sigmaTensor K L A σ e)

theorem mul_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (e : L ⊗[K] A) :
    e * AutomorphicForm.sigmaTensor K L A σ e = algebraMap A (L ⊗[K] A) (nrm K L A σ e) := by
  obtain ⟨hσσ, -⟩ := sigma_facts K L σ h2 hgen
  have hfix : AutomorphicForm.sigmaTensor K L A σ (e * AutomorphicForm.sigmaTensor K L A σ e) =
      e * AutomorphicForm.sigmaTensor K L A σ e := by
    rw [map_mul, sigmaTensor_sigmaTensor K L A σ hσσ, mul_comm]
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_sigmaTensor_eq K L A σ h2 hgen hfix
  rw [nrm, hr, pr_algebraMap]

theorem isUnit_iff_nrm_ne_zero (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (e : L ⊗[K] A) :
    IsUnit e ↔ nrm K L A σ e ≠ 0 := by
  have key := mul_sigmaTensor_eq K L A σ h2 hgen e
  constructor
  · intro he h0
    rw [h0, map_zero] at key
    have hu : IsUnit (e * AutomorphicForm.sigmaTensor K L A σ e) :=
      he.mul (he.map (AutomorphicForm.sigmaTensor K L A σ))
    rw [key] at hu
    exact not_isUnit_zero hu
  · intro hn
    refine IsUnit.of_mul_eq_one
      (AutomorphicForm.sigmaTensor K L A σ e * algebraMap A (L ⊗[K] A) (nrm K L A σ e)⁻¹) ?_
    rw [← mul_assoc, key, ← map_mul, mul_inv_cancel₀ hn, map_one]

theorem inverse_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {e : L ⊗[K] A} (he : IsUnit e) :
    Ring.inverse e =
      AutomorphicForm.sigmaTensor K L A σ e * algebraMap A (L ⊗[K] A) (nrm K L A σ e)⁻¹ := by
  have key := mul_sigmaTensor_eq K L A σ h2 hgen e
  have hn : nrm K L A σ e ≠ 0 := (isUnit_iff_nrm_ne_zero K L A σ h2 hgen e).mp he
  obtain ⟨u, rfl⟩ := he
  rw [Ring.inverse_unit]
  apply Units.inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, key, ← map_mul, mul_inv_cancel₀ hn, map_one]

end Algebra

section Scalars

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaGL_apply (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((AutomorphicForm.sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j
      = AutomorphicForm.sigmaTensor K L A σ ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j
      = (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A γ)
      = AutomorphicForm.toTensorGL K L A γ := by
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply]
  simp [AutomorphicForm.sigmaTensor]

def Z (a : Aˣ) : GL (Fin 2) (L ⊗[K] A) :=
  AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) a)

theorem Z_eq_scalar (a : Aˣ) :
    Z K L A a = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) : A →* L ⊗[K] A) a) := by
  ext i j
  rw [Z, toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem Z_mul_comm (a : Aˣ) (g : GL (Fin 2) (L ⊗[K] A)) : Z K L A a * g = g * Z K L A a := by
  rw [Z_eq_scalar]
  apply Units.ext
  push_cast
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem sigmaGL_Z (a : Aˣ) : AutomorphicForm.sigmaGL K L A σ (Z K L A a) = Z K L A a :=
  sigmaGL_toTensorGL K L A σ _

theorem Z_inv_mul (a : Aˣ) : Z K L A a⁻¹ * Z K L A a = 1 := by
  unfold Z
  rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]

end Scalars

section Descent

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem trace_map_ringHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (X : Matrix (Fin 2) (Fin 2) R) :
    (X.map f).trace = f X.trace := by
  simp [Matrix.trace_fin_two, Matrix.map_apply]

theorem map_sigma_eq_conj (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L A σ δ) :
    X.map (AutomorphicForm.sigmaTensor K L A σ) =
      ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  rw [AutomorphicForm.mem_twistedCommutant_iff] at hX
  rw [mul_assoc, hX, ← mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.GeneralLinearGroup.coe_one, one_mul]

theorem sigmaTensor_trace_eq (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L A σ δ) :
    AutomorphicForm.sigmaTensor K L A σ X.trace = X.trace := by
  rw [← trace_map_ringHom, map_sigma_eq_conj K L A σ δ X hX, Matrix.trace_mul_cycle,
    ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, one_mul]

theorem sigmaTensor_det_eq (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L A σ δ) :
    AutomorphicForm.sigmaTensor K L A σ X.det = X.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_sigma_eq_conj K L A σ δ X hX, Matrix.det_units_conj']

theorem trace_eq_algebraMap (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L A σ δ) :
    X.trace = algebraMap A (L ⊗[K] A) (pr K L A X.trace) := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_sigmaTensor_eq K L A σ h2 hgen (sigmaTensor_trace_eq K L A σ δ X hX)
  rw [hr, pr_algebraMap]

theorem det_eq_algebraMap (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L A σ δ) :
    X.det = algebraMap A (L ⊗[K] A) (pr K L A X.det) := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_sigmaTensor_eq K L A σ h2 hgen (sigmaTensor_det_eq K L A σ δ X hX)
  rw [hr, pr_algebraMap]

theorem newton_pr (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L A σ δ) (m : ℕ) :
    pr K L A (X ^ (m + 2)).trace =
      pr K L A X.trace * pr K L A (X ^ (m + 1)).trace - pr K L A X.det * pr K L A (X ^ m).trace := by
  have hinj : Function.Injective (algebraMap A (L ⊗[K] A)) := (algebraMap A (L ⊗[K] A)).injective
  apply hinj
  have hp : ∀ k : ℕ, X ^ k ∈ AutomorphicForm.twistedCommutant K L A σ δ := fun k => Subalgebra.pow_mem _ hX k
  rw [← trace_eq_algebraMap K L A σ h2 hgen δ _ (hp _), trace_pow_add_two, map_sub, map_mul, map_mul,
    ← trace_eq_algebraMap K L A σ h2 hgen δ _ hX, ← trace_eq_algebraMap K L A σ h2 hgen δ _ (hp _),
    ← det_eq_algebraMap K L A σ h2 hgen δ _ hX, ← trace_eq_algebraMap K L A σ h2 hgen δ _ (hp _)]

theorem pr_trace_one : pr K L A (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace = 2 := by
  have : (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace = algebraMap A (L ⊗[K] A) 2 := by
    rw [Matrix.trace_one, map_ofNat]; simp
  rw [this, pr_algebraMap]

theorem det_one_add {R : Type} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) :
    (1 + X).det = 1 + X.trace + X.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

end Descent

section Key

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem norm_pr_trace_le_one (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ)
    (hn : ‖pr K L (v.adicCompletion K) X.det‖ ≤ 1)
    (B : ℝ) (hB : ∀ m : ℕ, ‖pr K L (v.adicCompletion K) (X ^ m).trace‖ ≤ B) :
    ‖pr K L (v.adicCompletion K) X.trace‖ ≤ 1 := by
  by_contra ht
  push Not at ht
  refine not_bddAbove_newton (pr K L (v.adicCompletion K) X.trace) (pr K L (v.adicCompletion K) X.det) ht hn
    (fun m => pr K L (v.adicCompletion K) (X ^ m).trace) ?_ ?_ ?_ B hB
  · beta_reduce
    rw [pow_zero, pr_trace_one]

    have h2mem : (2 : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      have : ((2 : v.adicCompletionIntegers K) : v.adicCompletion K) = 2 := by push_cast; rfl
      rw [← this]; exact SetLike.coe_mem _
    exact Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp h2mem)
  · beta_reduce
    rw [pow_one]
  · intro m
    beta_reduce
    exact newton_pr K L (v.adicCompletion K) σ h2 hgen δ X hX m

theorem norm_algebraNorm_det_one_add_le (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hX : X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ)
    (hN : ‖Algebra.norm (v.adicCompletion K) X.det‖ ≤ 1)
    (B : ℝ) (hB : ∀ m : ℕ, ‖pr K L (v.adicCompletion K) (X ^ m).trace‖ ≤ B) :
    ‖Algebra.norm (v.adicCompletion K) (1 + X).det‖ ≤ 1 := by
  haveI : Module.Finite K L := Module.finite_of_finrank_eq_succ h2
  have hrank : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, h2]
  set t₀ := pr K L (v.adicCompletion K) X.trace with ht₀
  set n₀ := pr K L (v.adicCompletion K) X.det with hn₀
  have hdet : X.det = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) n₀ :=
    det_eq_algebraMap K L (v.adicCompletion K) σ h2 hgen δ X hX
  have htr : X.trace = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) t₀ :=
    trace_eq_algebraMap K L (v.adicCompletion K) σ h2 hgen δ X hX

  have hn : ‖n₀‖ ≤ 1 := by
    have h : Algebra.norm (v.adicCompletion K) X.det = n₀ ^ 2 := by
      rw [hdet, Algebra.norm_algebraMap, hrank]
    rw [h, norm_pow] at hN
    by_contra hc
    push Not at hc
    have : (1 : ℝ) < ‖n₀‖ ^ 2 := by nlinarith
    linarith
  have ht : ‖t₀‖ ≤ 1 := norm_pr_trace_le_one K L v σ h2 hgen δ X hX hn B hB
  have h1 : (1 + X).det = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (1 + t₀ + n₀) := by
    rw [det_one_add, htr, hdet, map_add, map_add, map_one]
  rw [h1, Algebra.norm_algebraMap, hrank, norm_pow]
  have hsum : ‖1 + t₀ + n₀‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hn)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ht)
  calc ‖1 + t₀ + n₀‖ ^ 2 ≤ 1 ^ 2 := by gcongr
    _ = 1 := one_pow 2

end Key

section Bound

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem continuous_pr' : Continuous (pr K L (v.adicCompletion K)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_algebraNorm' [Module.Finite K L] :
    Continuous (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  let b := Module.finBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  have h1 : Continuous fun x : L ⊗[K] v.adicCompletion K => Algebra.leftMulMatrix b x :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) =
      fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h2]
  exact h1.matrix_det

theorem algebraMap_eq_tmul' (a : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a = (1 : L) ⊗ₜ[K] a := rfl

theorem coe_Z_mul (e : (v.adicCompletion K)ˣ) (k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ((Z K L (v.adicCompletion K) e * k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (e : v.adicCompletion K) •
        (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
  ext i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, algebraMap_eq_tmul']
  simp only [Z, toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  fin_cases i <;> simp

theorem exists_bound_pr_trace (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ B : ℝ, ∀ X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ,
      ‖Algebra.norm (v.adicCompletion K) X.det‖ ≤ 1 → ‖pr K L (v.adicCompletion K) X.trace‖ ≤ B := by
  classical
  haveI : Module.Finite K L := Module.finite_of_finrank_eq_succ h2
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have hrank : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, h2]
  obtain ⟨C, hCc, hCT, hdec⟩ :=
    AutomorphicForm.exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδ hδq

  set f : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ :=
    fun k => ‖Algebra.norm (v.adicCompletion K) (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det‖ with hf
  set g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ :=
    fun k => ‖pr K L (v.adicCompletion K) (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).trace‖ with hg
  have hfc : Continuous f :=
    continuous_norm.comp ((continuous_algebraNorm' K L v).comp (Units.continuous_val.matrix_det))
  have hgc : Continuous g :=
    continuous_norm.comp ((continuous_pr' K L v).comp (Units.continuous_val.matrix_trace))

  have h1T : (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ := Subgroup.one_mem _
  obtain ⟨e₁, k₁, hk₁, -⟩ := hdec 1 h1T
  have hCne : C.Nonempty := ⟨k₁, hk₁⟩
  obtain ⟨kmin, hkminC, hkmin⟩ := hCc.exists_isMinOn hCne hfc.continuousOn
  obtain ⟨kmax, hkmaxC, hkmax⟩ := hCc.exists_isMaxOn hCne hgc.continuousOn
  set m₀ := f kmin with hm₀
  set M := g kmax with hM
  have hm₀pos : 0 < m₀ := by
    rw [hm₀, hf]
    refine norm_pos_iff.2 (IsUnit.ne_zero ?_)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit kmin)).map (Algebra.norm (v.adicCompletion K))
  have hM0 : 0 ≤ M := by rw [hM, hg]; exact norm_nonneg _
  refine ⟨max 1 m₀⁻¹ * M, fun X hX hN => ?_⟩
  by_cases hX0 : X = 0
  · rw [hX0, Matrix.trace_zero, map_zero, norm_zero]; positivity

  have hXD := (AutomorphicForm.mem_twistedCommutant_iff δ X).1 hX
  have hXu : IsUnit X :=
    AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen (v.adicCompletion K) c δ hδ hδq X hX0 (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) hXD.symm
  set u : GL (Fin 2) (L ⊗[K] v.adicCompletion K) := hXu.unit with hu
  have huX : (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = X := hXu.unit_spec
  have huT : u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :=
    (AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant δ u).2 (by rw [huX]; exact hX)
  obtain ⟨e, k, hkC, huk⟩ := hdec u huT

  have hXe : X = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (e : v.adicCompletion K) •
      (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
    rw [← huX, huk]; exact coe_Z_mul K L v e k
  have htr : pr K L (v.adicCompletion K) X.trace =
      (e : v.adicCompletion K) * pr K L (v.adicCompletion K) (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).trace := by
    rw [hXe, Matrix.trace_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hdet : Algebra.norm (v.adicCompletion K) X.det =
      (e : v.adicCompletion K) ^ 4 * Algebra.norm (v.adicCompletion K) (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det := by
    rw [hXe, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, Algebra.norm_algebraMap, hrank]
    ring

  have hfk : m₀ ≤ f k := hkmin hkC
  have hgk : g k ≤ M := hkmax hkC
  have he4 : ‖(e : v.adicCompletion K)‖ ^ 4 * m₀ ≤ 1 := by
    have : ‖(e : v.adicCompletion K)‖ ^ 4 * f k ≤ 1 := by
      rw [hf]; dsimp only
      rw [← norm_pow, ← norm_mul, ← hdet]; exact hN
    calc ‖(e : v.adicCompletion K)‖ ^ 4 * m₀ ≤ ‖(e : v.adicCompletion K)‖ ^ 4 * f k := by gcongr
      _ ≤ 1 := this
  have he : ‖(e : v.adicCompletion K)‖ ≤ max 1 m₀⁻¹ := by
    by_cases h1 : ‖(e : v.adicCompletion K)‖ ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push Not at h1
      have hp : ‖(e : v.adicCompletion K)‖ ≤ ‖(e : v.adicCompletion K)‖ ^ 4 := by
        calc ‖(e : v.adicCompletion K)‖ = ‖(e : v.adicCompletion K)‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖(e : v.adicCompletion K)‖ ^ 4 := pow_le_pow_right₀ h1.le (by norm_num)
      have h4 : ‖(e : v.adicCompletion K)‖ ^ 4 ≤ m₀⁻¹ := by
        rw [← one_div]; exact (le_div_iff₀ hm₀pos).mpr he4
      exact (hp.trans h4).trans (le_max_right _ _)
  calc ‖pr K L (v.adicCompletion K) X.trace‖
      = ‖(e : v.adicCompletion K)‖ * g k := by rw [htr, norm_mul, hg]
    _ ≤ max 1 m₀⁻¹ * M := by gcongr

end Bound

section Ultra

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem norm_algebraNorm_det_mul_le
    (X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hX : ‖Algebra.norm (v.adicCompletion K) X.det‖ ≤ 1) (hY : ‖Algebra.norm (v.adicCompletion K) Y.det‖ ≤ 1) :
    ‖Algebra.norm (v.adicCompletion K) (X * Y).det‖ ≤ 1 := by
  rw [Matrix.det_mul, map_mul, norm_mul]
  exact mul_le_one₀ hX (norm_nonneg _) hY

theorem norm_algebraNorm_det_add_le_of_le (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hXD : X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ)
    (hYD : Y ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ)
    (hY0 : Y ≠ 0)
    (hle : ‖Algebra.norm (v.adicCompletion K) X.det‖ ≤ ‖Algebra.norm (v.adicCompletion K) Y.det‖)
    (hY : ‖Algebra.norm (v.adicCompletion K) Y.det‖ ≤ 1) :
    ‖Algebra.norm (v.adicCompletion K) (X + Y).det‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := exists_bound_pr_trace K L v σ h2 hgen c δ hδ hδq

  have hYu : IsUnit Y :=
    AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen (v.adicCompletion K) c δ hδ hδq Y hY0 (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
      ((AutomorphicForm.mem_twistedCommutant_iff δ Y).1 hYD).symm
  set u : GL (Fin 2) (L ⊗[K] v.adicCompletion K) := hYu.unit with hu
  have huY : (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = Y := hYu.unit_spec
  have huT : u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :=
    (AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant δ u).2 (by rw [huY]; exact hYD)
  have huiD : ((u⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ :=
    (AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant δ u⁻¹).1 (Subgroup.inv_mem _ huT)

  set Z : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) :=
    ((u⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * X with hZ
  have hZD : Z ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ := Subalgebra.mul_mem _ huiD hXD
  have hYZ : Y * Z = X := by
    rw [hZ, ← huY, ← mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, one_mul]
  have hNpos : 0 < ‖Algebra.norm (v.adicCompletion K) Y.det‖ := by
    refine norm_pos_iff.2 (IsUnit.ne_zero ?_)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hYu).map (Algebra.norm (v.adicCompletion K))
  have hZN : ‖Algebra.norm (v.adicCompletion K) Z.det‖ ≤ 1 := by
    have h : ‖Algebra.norm (v.adicCompletion K) X.det‖ =
        ‖Algebra.norm (v.adicCompletion K) Y.det‖ * ‖Algebra.norm (v.adicCompletion K) Z.det‖ := by
      rw [← hYZ, Matrix.det_mul, map_mul, norm_mul]
    rw [h] at hle
    by_contra hc
    push Not at hc
    have : ‖Algebra.norm (v.adicCompletion K) Y.det‖ * 1 < ‖Algebra.norm (v.adicCompletion K) Y.det‖ *
        ‖Algebra.norm (v.adicCompletion K) Z.det‖ := mul_lt_mul_of_pos_left hc hNpos
    rw [mul_one] at this
    linarith

  have hBZ : ∀ m : ℕ, ‖pr K L (v.adicCompletion K) (Z ^ m).trace‖ ≤ B := by
    intro m
    refine hB _ (Subalgebra.pow_mem _ hZD m) ?_
    rw [Matrix.det_pow, map_pow, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hZN
  have hkey := norm_algebraNorm_det_one_add_le K L v σ h2 hgen δ Z hZD hZN B hBZ
  have hXY : X + Y = Y * (1 + Z) := by rw [mul_add, mul_one, hYZ, add_comm]
  rw [hXY]
  exact norm_algebraNorm_det_mul_le K L v Y (1 + Z) hY hkey

theorem norm_algebraNorm_det_add_le (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hXD : X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ)
    (hYD : Y ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ)
    (hX : ‖Algebra.norm (v.adicCompletion K) X.det‖ ≤ 1) (hY : ‖Algebra.norm (v.adicCompletion K) Y.det‖ ≤ 1) :
    ‖Algebra.norm (v.adicCompletion K) (X + Y).det‖ ≤ 1 := by
  by_cases hY0 : Y = 0
  · rw [hY0, add_zero]; exact hX
  by_cases hX0 : X = 0
  · rw [hX0, zero_add]; exact hY
  rcases le_total ‖Algebra.norm (v.adicCompletion K) X.det‖ ‖Algebra.norm (v.adicCompletion K) Y.det‖ with h | h
  · exact norm_algebraNorm_det_add_le_of_le K L v σ h2 hgen c δ hδ hδq X Y hXD hYD hY0 h hY
  · rw [add_comm]
    exact norm_algebraNorm_det_add_le_of_le K L v σ h2 hgen c δ hδ hδq Y X hYD hXD hX0 h hX

end Ultra

end Ws31.UltraNrd

namespace Ws31
namespace UltraNrd

section Sol

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem cond_iff_norm_le (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hxD : x ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ) :
    (x = 0 ∨ ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) ≤ 1 ∧
        Matrix.det x = (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) (s : v.adicCompletion K)) ↔
      ‖Algebra.norm (v.adicCompletion K) x.det‖ ≤ 1 := by
  haveI : Module.Finite K L := Module.finite_of_finrank_eq_succ h2
  have hrank : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, h2]
  have hincl : ∀ a : v.adicCompletion K,
      (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) a =
        algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a := fun a => rfl
  constructor
  · rintro (rfl | ⟨s, hs, hdet⟩)
    · rw [Matrix.det_zero, Algebra.norm_zero, norm_zero]; exact zero_le_one
    · rw [hdet, hincl, Algebra.norm_algebraMap, hrank, norm_pow]
      have hs' : ‖(s : v.adicCompletion K)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hs
      exact pow_le_one₀ (norm_nonneg _) hs'
  · intro hN
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    right
    have hxu : IsUnit x :=
      AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
        K L h2 σ hgen (v.adicCompletion K) c δ hδ hδq x hx0 (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
        ((AutomorphicForm.mem_twistedCommutant_iff δ x).1 hxD).symm
    set n₀ := pr K L (v.adicCompletion K) x.det with hn₀
    have hdet : x.det = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) n₀ :=
      det_eq_algebraMap K L (v.adicCompletion K) σ h2 hgen δ x hxD
    have hn0 : n₀ ≠ 0 := by
      intro h0
      have hdu : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det _).1 hxu
      rw [hdet, h0, map_zero] at hdu
      exact not_isUnit_zero hdu
    have hn1 : ‖n₀‖ ≤ 1 := by
      rw [hdet, Algebra.norm_algebraMap, hrank, norm_pow] at hN
      by_contra hc
      push Not at hc
      have : (1 : ℝ) < ‖n₀‖ ^ 2 := by nlinarith
      linarith
    refine ⟨Units.mk0 n₀ hn0, ?_, ?_⟩
    · rw [Units.val_mk0]; exact Valued.toNormedField.norm_le_one_iff.mp hn1
    · rw [Units.val_mk0, hincl]; exact hdet

end Sol

end Ws31.UltraNrd

open Ws31.UltraNrd in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (O : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hO : O = {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ∧
          (x = 0 ∨ ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) ≤ 1 ∧ Matrix.det x = (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) (s : v.adicCompletion K))}) :
    (0 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ O ∧ (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ O ∧
    (∀ x ∈ O, ∀ y ∈ O, x + y ∈ O) ∧ (∀ x ∈ O, -x ∈ O) ∧
    (∀ x ∈ O, ∀ y ∈ O, x * y ∈ O) ∧
    (∀ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K → ∀ x ∈ O, (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) a • x ∈ O) := by
  haveI : Module.Finite K L := Module.finite_of_finrank_eq_succ h2
  have hrank : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, h2]

  have hmem : ∀ x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      x ∈ O ↔ x ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ ∧
        ‖Algebra.norm (v.adicCompletion K) x.det‖ ≤ 1 := by
    intro x
    rw [hO, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hD, hc⟩
      have hxD : x ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ :=
        (AutomorphicForm.mem_twistedCommutant_iff δ x).2 hD
      exact ⟨hxD, (cond_iff_norm_le K L v σ h2 hgen c δ hδ hδq x hxD).1 hc⟩
    · rintro ⟨hxD, hN⟩
      exact ⟨(AutomorphicForm.mem_twistedCommutant_iff δ x).1 hxD,
        (cond_iff_norm_le K L v σ h2 hgen c δ hδ hδq x hxD).2 hN⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem]
    exact ⟨Subalgebra.zero_mem _, by rw [Matrix.det_zero, Algebra.norm_zero, norm_zero]; exact zero_le_one⟩
  · rw [hmem]
    exact ⟨Subalgebra.one_mem _, by rw [Matrix.det_one, map_one, norm_one]⟩
  · intro x hx y hy
    rw [hmem] at hx hy ⊢
    exact ⟨Subalgebra.add_mem _ hx.1 hy.1,
      norm_algebraNorm_det_add_le K L v σ h2 hgen c δ hδ hδq x y hx.1 hy.1 hx.2 hy.2⟩
  · intro x hx
    rw [hmem] at hx ⊢
    refine ⟨Subalgebra.neg_mem _ hx.1, ?_⟩
    have : (-x).det = x.det := by
      rw [Matrix.det_neg, Fintype.card_fin]; norm_num
    rw [this]; exact hx.2
  · intro x hx y hy
    rw [hmem] at hx hy ⊢
    exact ⟨Subalgebra.mul_mem _ hx.1 hy.1, norm_algebraNorm_det_mul_le K L v x y hx.2 hy.2⟩
  · intro a ha x hx
    rw [hmem] at hx ⊢
    refine ⟨AutomorphicForm.includeRight_smul_mem_twistedCommutant δ hx.1 a, ?_⟩
    have hincl : (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) a =
        algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a := rfl
    rw [hincl, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, Algebra.norm_algebraMap, hrank, norm_mul,
      norm_pow, norm_pow]
    have ha1 : ‖a‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp ha)
    exact mul_le_one₀ (pow_le_one₀ (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) ha1))
      (norm_nonneg _) hx.2

#print axioms solution

end
end S_AutomorphicForm_zero_mem_and_one_mem_and_add_mem_and_neg_mem_and_mul_mem_and_smul_mem_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar
end P2MW
export P2MW.S_AutomorphicForm_zero_mem_and_one_mem_and_add_mem_and_neg_mem_and_mul_mem_and_smul_mem_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar (solution)
