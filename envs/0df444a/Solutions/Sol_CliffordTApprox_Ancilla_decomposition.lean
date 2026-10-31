-- Prove2me | solution 1 for CliffordTApprox.Ancilla.decomposition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:24:17.917976+00:00
-- url     : https://prove2.me/submissions/50c40d4f-cf3e-48f9-aa98-4ae1217185b9

import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

def b0 : Qubits 1 := fun _ => false
def b1 : Qubits 1 := fun _ => true

def boolEquivQubits1 : Bool ≃ Qubits 1 where
  toFun b := fun _ => b
  invFun q := q 0
  left_inv b := rfl
  right_inv q := by
    ext i
    fin_cases i
    rfl

lemma boolEquivQubits1_false : boolEquivQubits1 false = b0 := rfl
lemma boolEquivQubits1_true : boolEquivQubits1 true = b1 := rfl

lemma matrix_ext_qubits1 (A B : Matrix (Qubits 1) (Qubits 1) ℂ)
    (h00 : A b0 b0 = B b0 b0)
    (h01 : A b0 b1 = B b0 b1)
    (h10 : A b1 b0 = B b1 b0)
    (h11 : A b1 b1 = B b1 b1) : A = B := by
  ext x y
  have hx : x = b0 ∨ x = b1 := by
    have : x 0 = false ∨ x 0 = true := by cases (x 0) <;> simp
    cases this with
    | inl h => left; ext i; fin_cases i; exact h
    | inr h => right; ext i; fin_cases i; exact h
  have hy : y = b0 ∨ y = b1 := by
    have : y 0 = false ∨ y 0 = true := by cases (y 0) <;> simp
    cases this with
    | inl h => left; ext i; fin_cases i; exact h
    | inr h => right; ext i; fin_cases i; exact h
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact h00
  · exact h01
  · exact h10
  · exact h11

lemma sum_qubits1 (f : Qubits 1 → ℂ) : (∑ k : Qubits 1, f k) = f b0 + f b1 := by
  rw [← boolEquivQubits1.sum_comp f]
  rw [Fintype.sum_bool]
  exact add_comm (f b1) (f b0)

lemma mul_qubits1 (A B : Matrix (Qubits 1) (Qubits 1) ℂ) (x y : Qubits 1) :
    (A * B) x y = A x b0 * B b0 y + A x b1 * B b1 y := by
  exact sum_qubits1 (fun k => A x k * B k y)

lemma phaseGate_00 (φ : ℝ) : phaseGate φ b0 b0 = 1 := by
  dsimp [phaseGate, oneQubit, Matrix.submatrix, Matrix.diagonal, b0]

lemma phaseGate_01 (φ : ℝ) : phaseGate φ b0 b1 = 0 := by
  dsimp [phaseGate, oneQubit, Matrix.submatrix, Matrix.diagonal, b0, b1]

lemma phaseGate_10 (φ : ℝ) : phaseGate φ b1 b0 = 0 := by
  dsimp [phaseGate, oneQubit, Matrix.submatrix, Matrix.diagonal, b0, b1]

lemma phaseGate_11 (φ : ℝ) : phaseGate φ b1 b1 = Complex.exp (φ * Complex.I) := by
  dsimp [phaseGate, oneQubit, Matrix.submatrix, Matrix.diagonal, b1]

lemma hadamard_00 : oneQubit hadamard b0 b0 = (Real.sqrt 2 : ℂ)⁻¹ := rfl
lemma hadamard_01 : oneQubit hadamard b0 b1 = (Real.sqrt 2 : ℂ)⁻¹ := rfl
lemma hadamard_10 : oneQubit hadamard b1 b0 = (Real.sqrt 2 : ℂ)⁻¹ := rfl
lemma hadamard_11 : oneQubit hadamard b1 b1 = -((Real.sqrt 2 : ℂ)⁻¹) := rfl

lemma inv_sqrt_two_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast; rfl
  have : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2 = 1 := by
    calc ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2
      _ = ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) := by rw [← h2]
      _ = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) := by ring
      _ = 1 * 1 := by
        have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
          norm_cast
          exact Real.sqrt_ne_zero'.mpr (by norm_num)
        rw [inv_mul_cancel₀ hne]
      _ = 1 := by ring
  linear_combination this / 2

noncomputable def X : Matrix (Qubits 1) (Qubits 1) ℂ :=
  oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard

lemma X_00 : X b0 b0 = 0 := by
  dsimp [X]
  simp_rw [mul_qubits1]
  simp [hadamard_00, hadamard_01, hadamard_10, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11, Complex.exp_pi_mul_I]

lemma X_01 : X b0 b1 = 1 := by
  dsimp [X]
  simp_rw [mul_qubits1]
  simp [hadamard_00, hadamard_01, hadamard_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11, Complex.exp_pi_mul_I]
  have h := inv_sqrt_two_sq
  linear_combination 2 * h

lemma X_10 : X b1 b0 = 1 := by
  dsimp [X]
  simp_rw [mul_qubits1]
  simp [hadamard_00, hadamard_10, hadamard_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11, Complex.exp_pi_mul_I]
  have h := inv_sqrt_two_sq
  linear_combination 2 * h

lemma X_11 : X b1 b1 = 0 := by
  dsimp [X]
  simp_rw [mul_qubits1]
  simp [hadamard_01, hadamard_10, hadamard_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11, Complex.exp_pi_mul_I]

noncomputable def G (θ : ℝ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  phaseGate θ * X * phaseGate θ * X

lemma G_00 (θ : ℝ) : G θ b0 b0 = Complex.exp (θ * Complex.I) := by
  dsimp [G]
  simp_rw [mul_qubits1]
  simp [X_00, X_01, X_10, X_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]

lemma G_01 (θ : ℝ) : G θ b0 b1 = 0 := by
  dsimp [G]
  simp_rw [mul_qubits1]
  simp [X_00, X_01, X_10, X_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]

lemma G_10 (θ : ℝ) : G θ b1 b0 = 0 := by
  dsimp [G]
  simp_rw [mul_qubits1]
  simp [X_00, X_01, X_10, X_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]

lemma G_11 (θ : ℝ) : G θ b1 b1 = Complex.exp (θ * Complex.I) := by
  dsimp [G]
  simp_rw [mul_qubits1]
  simp [X_00, X_01, X_10, X_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]

lemma G_mul (θ : ℝ) (M : Matrix (Qubits 1) (Qubits 1) ℂ) (x y : Qubits 1) :
    (G θ * M) x y = Complex.exp (θ * Complex.I) * M x y := by
  rw [mul_qubits1]
  have hx : x = b0 ∨ x = b1 := by
    have : x 0 = false ∨ x 0 = true := by cases (x 0) <;> simp
    cases this with
    | inl h => left; ext i; fin_cases i; exact h
    | inr h => right; ext i; fin_cases i; exact h
  rcases hx with rfl | rfl
  · rw [G_00, G_01, zero_mul, add_zero]
  · rw [G_10, G_11, zero_mul, zero_add]

noncomputable def R (φ₁ φ₂ φ₃ : ℝ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard * phaseGate φ₃

lemma R_00 (φ₁ φ₂ φ₃ : ℝ) :
    R φ₁ φ₂ φ₃ b0 b0 = (1 + Complex.exp (φ₂ * Complex.I)) / 2 := by
  dsimp [R]
  simp_rw [mul_qubits1]
  simp [hadamard_00, hadamard_01, hadamard_10, hadamard_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]
  have h := inv_sqrt_two_sq
  linear_combination (1 + Complex.exp (φ₂ * Complex.I)) * h

lemma R_01 (φ₁ φ₂ φ₃ : ℝ) :
    R φ₁ φ₂ φ₃ b0 b1 = (1 - Complex.exp (φ₂ * Complex.I)) / 2 * Complex.exp (φ₃ * Complex.I) := by
  dsimp [R]
  simp_rw [mul_qubits1]
  simp [hadamard_00, hadamard_01, hadamard_10, hadamard_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]
  have h := inv_sqrt_two_sq
  linear_combination (1 - Complex.exp (φ₂ * Complex.I)) * h

lemma R_10 (φ₁ φ₂ φ₃ : ℝ) :
    R φ₁ φ₂ φ₃ b1 b0 = Complex.exp (φ₁ * Complex.I) * (1 - Complex.exp (φ₂ * Complex.I)) / 2 := by
  dsimp [R]
  simp_rw [mul_qubits1]
  simp [hadamard_00, hadamard_01, hadamard_10, hadamard_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]
  have h := inv_sqrt_two_sq
  linear_combination Complex.exp (φ₁ * Complex.I) * (1 - Complex.exp (φ₂ * Complex.I)) * h

lemma R_11 (φ₁ φ₂ φ₃ : ℝ) :
    R φ₁ φ₂ φ₃ b1 b1 = Complex.exp (φ₁ * Complex.I) * Complex.exp (φ₃ * Complex.I) * (1 + Complex.exp (φ₂ * Complex.I)) / 2 := by
  dsimp [R]
  simp_rw [mul_qubits1]
  simp [hadamard_00, hadamard_01, hadamard_10, hadamard_11, phaseGate_00, phaseGate_01, phaseGate_10, phaseGate_11]
  have h := inv_sqrt_two_sq
  linear_combination Complex.exp (φ₁ * Complex.I) * Complex.exp (φ₃ * Complex.I) * (1 + Complex.exp (φ₂ * Complex.I)) * h

lemma target_eq_G_mul_R (θ φ₁ φ₂ φ₃ : ℝ) :
    phaseGate θ * (oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard) *
        phaseGate θ * (oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard) *
        phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard * phaseGate φ₃ =
    G θ * R φ₁ φ₂ φ₃ := by
  dsimp [G, R, X]
  simp only [mul_assoc]

lemma exp_mul_cos (α : ℝ) :
    Complex.exp (α * Complex.I) * (Real.cos α : ℂ) =
    (1 + Complex.exp (2 * α * Complex.I)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  have h1 : Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((α : ℂ) * Complex.I) =
      Complex.exp (2 * (α : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : Complex.exp ((α : ℂ) * Complex.I) * Complex.exp (-((α : ℂ)) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have : (α : ℂ) * Complex.I + -↑α * Complex.I = 0 := by ring
    rw [this, Complex.exp_zero]
  have h3 : Complex.exp ((α : ℂ) * Complex.I) *
      ((Complex.exp ((α : ℂ) * Complex.I) + Complex.exp (-((α : ℂ)) * Complex.I)) / 2) =
      (Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((α : ℂ) * Complex.I) +
       Complex.exp ((α : ℂ) * Complex.I) * Complex.exp (-((α : ℂ)) * Complex.I)) / 2 := by ring
  rw [h3, h1, h2]; ring

lemma exp_mul_sin (α : ℝ) :
    -Complex.I * Complex.exp (α * Complex.I) * (Real.sin α : ℂ) =
    (1 - Complex.exp (2 * α * Complex.I)) / 2 := by
  rw [Complex.ofReal_sin, Complex.sin]
  have h1 : Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((α : ℂ) * Complex.I) =
      Complex.exp (2 * (α : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : Complex.exp ((α : ℂ) * Complex.I) * Complex.exp (-((α : ℂ)) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have : (α : ℂ) * Complex.I + -↑α * Complex.I = 0 := by ring
    rw [this, Complex.exp_zero]
  have h3 : -Complex.I * Complex.exp ((α : ℂ) * Complex.I) *
      ((Complex.exp (-((α : ℂ)) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) * Complex.I / 2) =
      (-Complex.I * Complex.I) *
      (Complex.exp ((α : ℂ) * Complex.I) * Complex.exp (-((α : ℂ)) * Complex.I) -
       Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((α : ℂ) * Complex.I)) / 2 := by ring
  have hI : -Complex.I * Complex.I = 1 := by
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination -this
  rw [h3, hI, h1, h2]; ring

lemma exp_pi_div_two_mul_I : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  have : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.cos ((Real.pi / 2 : ℝ) : ℂ) + Complex.sin ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
  rw [this]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma entry_00_match (θ' α : ℝ) :
    Complex.exp ((θ' - α) * Complex.I) * (1 + Complex.exp (2 * α * Complex.I)) / 2 =
    Complex.exp (θ' * Complex.I) * (Real.cos α : ℂ) := by
  have h := exp_mul_cos α
  have h_assoc : Complex.exp ((θ' - α) * Complex.I) * (1 + Complex.exp (2 * α * Complex.I)) / 2 =
      Complex.exp ((θ' - α) * Complex.I) * ((1 + Complex.exp (2 * α * Complex.I)) / 2) := by ring
  rw [h_assoc, ← h]
  have : Complex.exp ((θ' - α) * Complex.I) * (Complex.exp (α * Complex.I) * (Real.cos α : ℂ)) =
      (Complex.exp ((θ' - α) * Complex.I) * Complex.exp (α * Complex.I)) * (Real.cos α : ℂ) := by ring
  rw [this, ← Complex.exp_add]
  congr 2
  ring

lemma test_ring_10 (θ' α ψ₁ : ℝ) :
    (θ' - α) * Complex.I + (ψ₁ - θ' + Real.pi / 2) * Complex.I + α * Complex.I =
    ψ₁ * Complex.I + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

lemma h_exp_eq_10 (θ' α ψ₁ : ℝ) :
    Complex.exp ((θ' - α) * Complex.I + (ψ₁ - θ' + Real.pi / 2) * Complex.I + α * Complex.I) =
    Complex.exp (ψ₁ * Complex.I) * Complex.I := by
  conv_rhs => enter [2]; rw [← exp_pi_div_two_mul_I]
  rw [← Complex.exp_add]
  exact congr_arg Complex.exp (test_ring_10 θ' α ψ₁)

lemma entry_10_match (θ' α ψ₁ : ℝ) :
    Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      (1 - Complex.exp (2 * α * Complex.I)) / 2 =
    Complex.exp (ψ₁ * Complex.I) * (Real.sin α : ℂ) := by
  have h := exp_mul_sin α
  have hI : Complex.I * -Complex.I = 1 := by
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination -this
  have h_assoc : Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      (1 - Complex.exp (2 * α * Complex.I)) / 2 =
      Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      ((1 - Complex.exp (2 * α * Complex.I)) / 2) := by ring
  rw [h_assoc, ← h]
  have h_exp : Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      (-Complex.I * Complex.exp (α * Complex.I) * (Real.sin α : ℂ)) =
      (Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
       Complex.exp (α * Complex.I)) * -Complex.I * (Real.sin α : ℂ) := by ring
  rw [h_exp, ← Complex.exp_add, ← Complex.exp_add]
  rw [h_exp_eq_10]
  have : Complex.exp (ψ₁ * Complex.I) * Complex.I * -Complex.I * (Real.sin α : ℂ) =
      Complex.exp (ψ₁ * Complex.I) * (Complex.I * -Complex.I) * (Real.sin α : ℂ) := by ring
  rw [this, hI]
  ring

lemma entry_01_match (θ' α ψ₃ : ℝ) :
    Complex.exp ((θ' - α) * Complex.I) * (1 - Complex.exp (2 * α * Complex.I)) / 2 *
      Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) =
    Complex.exp (ψ₃ * Complex.I) * (Real.sin α : ℂ) := by
  have h : Complex.exp ((θ' - α) * Complex.I) * (1 - Complex.exp (2 * α * Complex.I)) / 2 *
      Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) =
      Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) *
      (1 - Complex.exp (2 * α * Complex.I)) / 2 := by ring
  rw [h]
  exact entry_10_match θ' α ψ₃

lemma test_ring_11 (θ' α ψ₁ ψ₃ : ℝ) :
    (θ' - α) * Complex.I + (ψ₁ - θ' + Real.pi / 2) * Complex.I +
      (ψ₃ - θ' + Real.pi / 2) * Complex.I + α * Complex.I =
    (ψ₁ + ψ₃ - θ') * Complex.I + (Real.pi : ℂ) * Complex.I := by
  push_cast; ring

lemma h_exp_eq_11 (θ' α ψ₁ ψ₃ : ℝ) :
    Complex.exp ((θ' - α) * Complex.I + (ψ₁ - θ' + Real.pi / 2) * Complex.I +
      (ψ₃ - θ' + Real.pi / 2) * Complex.I + α * Complex.I) =
    -Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I) := by
  have h_pi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have : -Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I) =
      Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I) * Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [h_pi]; ring
  rw [this, ← Complex.exp_add]
  exact congr_arg Complex.exp (test_ring_11 θ' α ψ₁ ψ₃)

lemma entry_11_match (θ' α ψ₁ ψ₃ : ℝ) :
    Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) *
      (1 + Complex.exp (2 * α * Complex.I)) / 2 =
    -(Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I) * (Real.cos α : ℂ)) := by
  have h := exp_mul_cos α
  have h_assoc : Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) *
      (1 + Complex.exp (2 * α * Complex.I)) / 2 =
      Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) *
      ((1 + Complex.exp (2 * α * Complex.I)) / 2) := by ring
  rw [h_assoc, ← h]
  have h_exp : Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
      Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) *
      (Complex.exp (α * Complex.I) * (Real.cos α : ℂ)) =
      (Complex.exp ((θ' - α) * Complex.I) * Complex.exp ((ψ₁ - θ' + Real.pi / 2) * Complex.I) *
       Complex.exp ((ψ₃ - θ' + Real.pi / 2) * Complex.I) *
       Complex.exp (α * Complex.I)) * (Real.cos α : ℂ) := by ring
  rw [h_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  rw [h_exp_eq_11]
  ring

lemma star_exp_ofReal_mul_I (x : ℝ) :
    star (Complex.exp (x * Complex.I)) = Complex.exp (-x * Complex.I) := by
  have h : (starRingEnd ℂ) ((x : ℂ) * Complex.I) = -x * Complex.I := by
    simp
  change (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj, h]

lemma star_eq_norm_mul_exp_neg_arg (z : ℂ) :
    star z = (‖z‖ : ℂ) * Complex.exp (-z.arg * Complex.I) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [star_mul, star_exp_ofReal_mul_I]
  simp only [RCLike.star_def, Complex.conj_ofReal]
  ring

lemma star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  change (starRingEnd ℂ) z * z = _
  rw [← Complex.normSq_eq_conj_mul_self]
  congr 1
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]

lemma full_11_star_eq (θ' ψ₁ ψ₃ : ℝ) (r00 r10 r01 : ℝ) (hr : r10 = r01) :
    ((r10 : ℂ) * Complex.exp (-ψ₁ * Complex.I)) *
      (-(Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I) * (r00 : ℂ))) =
    - (((r00 : ℂ) * Complex.exp (-θ' * Complex.I)) *
       ((r01 : ℂ) * Complex.exp (ψ₃ * Complex.I))) := by
  have h1 : Complex.exp (-ψ₁ * Complex.I) * Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I) =
      Complex.exp ((ψ₃ - θ') * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h2 : Complex.exp ((ψ₃ - θ') * Complex.I) =
      Complex.exp (-θ' * Complex.I) * Complex.exp (ψ₃ * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have : ((r10 : ℂ) * Complex.exp (-ψ₁ * Complex.I)) *
      (-(Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I) * (r00 : ℂ))) =
      - ((r10 : ℂ) * (r00 : ℂ) * (Complex.exp (-ψ₁ * Complex.I) * Complex.exp ((ψ₁ + ψ₃ - θ') * Complex.I))) := by ring
  rw [this, h1, h2, hr]
  ring

lemma norm_relations (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + b ^ 2 = 1) :
    a ≤ 1 ∧ Real.cos (Real.arccos a) = a ∧ Real.sin (Real.arccos a) = b := by
  have ha2 : a ^ 2 ≤ 1 := by
    have : 0 ≤ b ^ 2 := by positivity
    linarith
  have ha1 : a ≤ 1 := by
    nlinarith
  have hcos : Real.cos (Real.arccos a) = a :=
    Real.cos_arccos (by linarith) ha1
  have hsin : Real.sin (Real.arccos a) = b := by
    rw [Real.sin_arccos]
    have : 1 - a ^ 2 = b ^ 2 := by linarith
    rw [this, Real.sqrt_sq hb]
  exact ⟨ha1, hcos, hsin⟩

theorem solution (U : Matrix (Qubits 1) (Qubits 1) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 1) ℂ) :
    ∃ θ φ₁ φ₂ φ₃ : ℝ,
      U = phaseGate θ * (oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard) *
        phaseGate θ * (oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard) *
        phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard * phaseGate φ₃ := by
  have h_star_mul : star U * U = 1 := (Matrix.mem_unitaryGroup_iff'.mp hU)
  have h_mul_star : U * star U = 1 := (Matrix.mem_unitaryGroup_iff.mp hU)
  by_cases hu10 : U b1 b0 = 0
  · -- Case 1: U b1 b0 = 0 (diagonal unitary)
    have hu00_norm : ‖U b0 b0‖ = 1 := by
      have h := congr_fun (congr_fun h_star_mul b0) b0
      rw [mul_qubits1, Matrix.one_apply_eq, Matrix.star_apply, Matrix.star_apply, hu10] at h
      simp only [mul_zero, add_zero] at h
      rw [star_mul_self] at h
      have h_re : ((‖U b0 b0‖ ^ 2 : ℝ) : ℂ).re = (1 : ℂ).re := by rw [h]
      simp only [Complex.ofReal_re, Complex.one_re] at h_re
      have hpos : 0 ≤ ‖U b0 b0‖ := norm_nonneg _
      nlinarith
    have hu01 : U b0 b1 = 0 := by
      have h := congr_fun (congr_fun h_mul_star b0) b0
      rw [mul_qubits1, Matrix.one_apply_eq, Matrix.star_apply, Matrix.star_apply] at h
      rw [mul_comm (U b0 b0), star_mul_self, hu00_norm] at h
      have : (1 : ℂ) + U b0 b1 * star (U b0 b1) = 1 := by
        simp only [Complex.ofReal_one, one_pow] at h
        exact h
      have h_prod : U b0 b1 * star (U b0 b1) = 0 := by linear_combination this
      rw [mul_comm, star_mul_self] at h_prod
      have h_re : ((‖U b0 b1‖ ^ 2 : ℝ) : ℂ).re = (0 : ℂ).re := by rw [h_prod]
      simp only [Complex.ofReal_re, Complex.zero_re] at h_re
      have h_norm : ‖U b0 b1‖ = 0 := by
        have hpos : 0 ≤ ‖U b0 b1‖ := norm_nonneg _
        nlinarith
      exact norm_eq_zero.mp h_norm
    have hu11_norm : ‖U b1 b1‖ = 1 := by
      have h := congr_fun (congr_fun h_star_mul b1) b1
      rw [mul_qubits1, Matrix.one_apply_eq, Matrix.star_apply, Matrix.star_apply, hu01] at h
      simp only [mul_zero, zero_add] at h
      rw [star_mul_self] at h
      have h_re : ((‖U b1 b1‖ ^ 2 : ℝ) : ℂ).re = (1 : ℂ).re := by rw [h]
      simp only [Complex.ofReal_re, Complex.one_re] at h_re
      have hpos : 0 ≤ ‖U b1 b1‖ := norm_nonneg _
      nlinarith
    use (U b0 b0).arg, ((U b1 b1).arg - (U b0 b0).arg), 0, 0
    rw [target_eq_G_mul_R]
    apply matrix_ext_qubits1
    · rw [G_mul, R_00]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      have : Complex.exp ((U b0 b0).arg * Complex.I) * ((1 + 1) / 2) =
          Complex.exp ((U b0 b0).arg * Complex.I) := by ring
      rw [this]
      have h := Complex.norm_mul_exp_arg_mul_I (U b0 b0)
      rw [hu00_norm] at h
      simp only [Complex.ofReal_one, one_mul] at h
      exact h.symm
    · rw [hu01, G_mul, R_01]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      ring
    · rw [hu10, G_mul, R_10]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      ring
    · rw [G_mul, R_11]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      have h_mul : Complex.exp ((U b0 b0).arg * Complex.I) *
          (Complex.exp (((U b1 b1).arg - (U b0 b0).arg) * Complex.I) * 1 * (1 + 1) / 2) =
          Complex.exp ((U b0 b0).arg * Complex.I) *
          Complex.exp (((U b1 b1).arg - (U b0 b0).arg) * Complex.I) := by ring
      rw [h_mul, ← Complex.exp_add]
      have h_arg : ((U b0 b0).arg : ℂ) * Complex.I + (((U b1 b1).arg : ℂ) - ((U b0 b0).arg : ℂ)) * Complex.I =
          ((U b1 b1).arg : ℂ) * Complex.I := by ring
      rw [h_arg]
      have h := Complex.norm_mul_exp_arg_mul_I (U b1 b1)
      rw [hu11_norm] at h
      simp only [Complex.ofReal_one, one_mul] at h
      exact h.symm
  · -- Case 2: U b1 b0 ≠ 0
    have h_norm_sum_col : ‖U b0 b0‖ ^ 2 + ‖U b1 b0‖ ^ 2 = 1 := by
      have h := congr_fun (congr_fun h_star_mul b0) b0
      rw [mul_qubits1, Matrix.one_apply_eq, Matrix.star_apply, Matrix.star_apply] at h
      rw [star_mul_self, star_mul_self] at h
      have h_re : (((‖U b0 b0‖ ^ 2 + ‖U b1 b0‖ ^ 2 : ℝ) : ℂ)).re = (1 : ℂ).re := by
        have : ((‖U b0 b0‖ ^ 2 : ℝ) : ℂ) + ((‖U b1 b0‖ ^ 2 : ℝ) : ℂ) =
            (((‖U b0 b0‖ ^ 2 + ‖U b1 b0‖ ^ 2 : ℝ) : ℂ)) := by push_cast; rfl
        rw [← this, h]
      simp only [Complex.ofReal_re, Complex.one_re] at h_re
      exact h_re
    have h_norm_sum_row : ‖U b0 b0‖ ^ 2 + ‖U b0 b1‖ ^ 2 = 1 := by
      have h := congr_fun (congr_fun h_mul_star b0) b0
      rw [mul_qubits1, Matrix.one_apply_eq, Matrix.star_apply, Matrix.star_apply] at h
      rw [mul_comm (U b0 b0), mul_comm (U b0 b1), star_mul_self, star_mul_self] at h
      have h_re : (((‖U b0 b0‖ ^ 2 + ‖U b0 b1‖ ^ 2 : ℝ) : ℂ)).re = (1 : ℂ).re := by
        have : ((‖U b0 b0‖ ^ 2 : ℝ) : ℂ) + ((‖U b0 b1‖ ^ 2 : ℝ) : ℂ) =
            (((‖U b0 b0‖ ^ 2 + ‖U b0 b1‖ ^ 2 : ℝ) : ℂ)) := by push_cast; rfl
        rw [← this, h]
      simp only [Complex.ofReal_re, Complex.one_re] at h_re
      exact h_re
    have h_norm_eq : ‖U b1 b0‖ = ‖U b0 b1‖ := by
      have hsq : ‖U b1 b0‖ ^ 2 = ‖U b0 b1‖ ^ 2 := by linarith [h_norm_sum_col, h_norm_sum_row]
      nlinarith [norm_nonneg (U b1 b0), norm_nonneg (U b0 b1)]
    have h_rel := norm_relations ‖U b0 b0‖ ‖U b1 b0‖ (norm_nonneg _) (norm_nonneg _) h_norm_sum_col
    have hcos : Real.cos (Real.arccos ‖U b0 b0‖) = ‖U b0 b0‖ := h_rel.2.1
    have hsin : Real.sin (Real.arccos ‖U b0 b0‖) = ‖U b1 b0‖ := h_rel.2.2
    let α := Real.arccos ‖U b0 b0‖
    let θ' := (U b0 b0).arg
    let θ := θ' - α
    let φ₁ := (U b1 b0).arg - θ' + Real.pi / 2
    let φ₂ := 2 * α
    let φ₃ := (U b0 b1).arg - θ' + Real.pi / 2
    use θ, φ₁, φ₂, φ₃
    rw [target_eq_G_mul_R]
    apply matrix_ext_qubits1
    · rw [G_mul, R_00]
      have : Complex.exp (θ * Complex.I) * ((1 + Complex.exp (φ₂ * Complex.I)) / 2) =
          Complex.exp (θ * Complex.I) * (1 + Complex.exp (φ₂ * Complex.I)) / 2 := by ring
      rw [this]
      dsimp only [θ, φ₂]
      push_cast
      have h_entry := entry_00_match θ' α
      rw [h_entry, hcos]
      have h := Complex.norm_mul_exp_arg_mul_I (U b0 b0)
      rw [mul_comm]
      exact h.symm
    · rw [G_mul, R_01]
      have : Complex.exp (θ * Complex.I) * ((1 - Complex.exp (φ₂ * Complex.I)) / 2 * Complex.exp (φ₃ * Complex.I)) =
          Complex.exp (θ * Complex.I) * (1 - Complex.exp (φ₂ * Complex.I)) / 2 * Complex.exp (φ₃ * Complex.I) := by ring
      rw [this]
      dsimp only [θ, φ₂, φ₃]
      push_cast
      have h_entry := entry_01_match θ' α (U b0 b1).arg
      rw [h_entry, hsin, h_norm_eq]
      have h := Complex.norm_mul_exp_arg_mul_I (U b0 b1)
      rw [mul_comm]
      exact h.symm
    · rw [G_mul, R_10]
      have : Complex.exp (θ * Complex.I) * (Complex.exp (φ₁ * Complex.I) * (1 - Complex.exp (φ₂ * Complex.I)) / 2) =
          Complex.exp (θ * Complex.I) * Complex.exp (φ₁ * Complex.I) * (1 - Complex.exp (φ₂ * Complex.I)) / 2 := by ring
      rw [this]
      dsimp only [θ, φ₁, φ₂]
      push_cast
      have h_entry := entry_10_match θ' α (U b1 b0).arg
      rw [h_entry, hsin]
      have h := Complex.norm_mul_exp_arg_mul_I (U b1 b0)
      rw [mul_comm]
      exact h.symm
    · -- b1 b1
      have h_ortho : star (U b0 b0) * U b0 b1 + star (U b1 b0) * U b1 b1 = 0 := by
        have h := congr_fun (congr_fun h_star_mul b0) b1
        have hne : b0 ≠ b1 := by
          intro heq
          have : b0 0 = b1 0 := congr_fun heq 0
          revert this
          decide
        rw [mul_qubits1, Matrix.one_apply_ne hne, Matrix.star_apply, Matrix.star_apply] at h
        exact h
      have h_prod : star (U b1 b0) * U b1 b1 = - (star (U b0 b0) * U b0 b1) := by
        linear_combination h_ortho
      have h_full_11 : (G θ * R φ₁ φ₂ φ₃) b1 b1 =
          -(Complex.exp (((U b1 b0).arg + (U b0 b1).arg - θ') * Complex.I) * (‖U b0 b0‖ : ℂ)) := by
        have h_assoc : (G θ * R φ₁ φ₂ φ₃) b1 b1 =
            Complex.exp (θ * Complex.I) * Complex.exp (φ₁ * Complex.I) *
              Complex.exp (φ₃ * Complex.I) * (1 + Complex.exp (φ₂ * Complex.I)) / 2 := by
          rw [G_mul, R_11]; ring
        rw [h_assoc]
        dsimp only [θ, φ₁, φ₂, φ₃]
        push_cast
        have h_entry := entry_11_match θ' α (U b1 b0).arg (U b0 b1).arg
        rw [h_entry, hcos]
      have h_star_full : star (U b1 b0) * (G θ * R φ₁ φ₂ φ₃) b1 b1 = - (star (U b0 b0) * U b0 b1) := by
        rw [h_full_11]
        conv_lhs =>
          enter [1]
          rw [star_eq_norm_mul_exp_neg_arg]
        have h_id := full_11_star_eq θ' (U b1 b0).arg (U b0 b1).arg
          ‖U b0 b0‖ ‖U b1 b0‖ ‖U b0 b1‖ h_norm_eq
        rw [h_id]
        have h_u01 := Complex.norm_mul_exp_arg_mul_I (U b0 b1)
        rw [h_u01]
        have h_u00_star : star (U b0 b0) = (‖U b0 b0‖ : ℂ) * Complex.exp (-θ' * Complex.I) :=
          star_eq_norm_mul_exp_neg_arg (U b0 b0)
        rw [← h_u00_star]
      have h_eq_mul : star (U b1 b0) * (G θ * R φ₁ φ₂ φ₃) b1 b1 = star (U b1 b0) * U b1 b1 := by
        rw [h_star_full, h_prod]
      have h_star_ne : star (U b1 b0) ≠ 0 := by
        intro h_zero
        apply hu10
        have h_double_star : U b1 b0 = star (star (U b1 b0)) := (star_star (U b1 b0)).symm
        rw [h_double_star, h_zero, star_zero]
      exact (mul_left_cancel₀ h_star_ne h_eq_mul).symm
