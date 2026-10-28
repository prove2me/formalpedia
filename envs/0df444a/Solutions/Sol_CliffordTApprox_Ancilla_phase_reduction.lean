-- Prove2me | solution 1 for CliffordTApprox.Ancilla.phase_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:04:51.755921+00:00
-- url     : https://prove2.me/submissions/8d93cc40-3c28-452d-a4eb-3b5df714e379

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace Aux_CliffordTApprox_Ancilla_phase_reduction
open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

lemma oneQubit_eq (M : Matrix Bool Bool ℂ) :
    oneQubit M = M.submatrix (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool) := rfl

lemma oneQubit_mul (M N : Matrix Bool Bool ℂ) : oneQubit M * oneQubit N = oneQubit (M * N) := by
  rw [oneQubit_eq, oneQubit_eq, oneQubit_eq, Matrix.submatrix_mul_equiv]

lemma T_mul_phase (ψ : ℝ) : oneQubit gateT * phaseGate ψ = phaseGate (Real.pi / 4 + ψ) := by
  unfold phaseGate
  rw [oneQubit_mul]
  congr 1
  unfold gateT
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  cases a
  · simp
  · simp only [ite_true]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

lemma pow_mul_phase (m : ℕ) : ∀ ψ : ℝ,
    oneQubit gateT ^ m * phaseGate ψ = phaseGate (m * (Real.pi / 4) + ψ) := by
  induction m with
  | zero => intro ψ; simp
  | succ n ih =>
    intro ψ
    rw [pow_succ, mul_assoc, T_mul_phase, ih]
    congr 1
    push_cast
    ring

lemma phase_periodic (ψ : ℝ) (k : ℤ) : phaseGate (ψ + k * (2 * Real.pi)) = phaseGate ψ := by
  unfold phaseGate
  congr 2
  funext a
  cases a
  · simp
  · simp only [ite_true]
    have : ((ψ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I = ψ * Complex.I + k * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end Aux_CliffordTApprox_Ancilla_phase_reduction

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12 CliffordTApprox.Ancilla
  Aux_CliffordTApprox_Ancilla_phase_reduction in
theorem solution (φ : ℝ) :
    ∃ m : ℕ, m < 8 ∧ ∃ φ' : ℝ, 0 ≤ φ' ∧ φ' ≤ Real.pi / 4 ∧
      phaseGate φ = oneQubit gateT ^ m * phaseGate φ' := by
  have hp : 0 < Real.pi / 4 := by positivity
  set n : ℤ := ⌊φ / (Real.pi / 4)⌋ with hn
  have h1 : (n : ℝ) ≤ φ / (Real.pi / 4) := Int.floor_le _
  have h2 : φ / (Real.pi / 4) < n + 1 := Int.lt_floor_add_one _
  refine ⟨(n % 8).toNat, ?_, φ - n * (Real.pi / 4), ?_, ?_, ?_⟩
  · have := Int.emod_lt_of_pos n (by norm_num : (0:ℤ) < 8)
    have := Int.emod_nonneg n (by norm_num : (8:ℤ) ≠ 0)
    omega
  · rw [le_div_iff₀ hp] at h1; linarith
  · rw [div_lt_iff₀ hp] at h2; linarith
  · rw [pow_mul_phase]
    have h0 := Int.emod_nonneg n (by norm_num : (8:ℤ) ≠ 0)
    have hcast : (((n % 8).toNat : ℕ) : ℝ) = ((n % 8 : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    have hdiv : n = n % 8 + 8 * (n / 8) := by omega
    rw [hcast, ← phase_periodic _ (-(n / 8))]
    congr 1
    have : (n : ℝ) = ((n % 8 : ℤ) : ℝ) + 8 * ((n / 8 : ℤ) : ℝ) := by
      conv_lhs => rw [hdiv]
      push_cast; ring
    rw [this]; push_cast; ring
