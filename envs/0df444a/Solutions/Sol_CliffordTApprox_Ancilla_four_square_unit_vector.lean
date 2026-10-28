-- Prove2me | solution 1 for CliffordTApprox.Ancilla.four_square_unit_vector
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:08:41.399809+00:00
-- url     : https://prove2.me/submissions/a7c91858-2a51-4b32-8cc6-d3892837cc98

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace Aux_CliffordTApprox_Ancilla_four_square_unit_vector
open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

lemma nsq (x y : ℤ) (k : ℕ) :
    ‖((x : ℂ) + (y : ℂ) * Complex.I) / (2 : ℂ) ^ k‖ ^ 2 = ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) / ((2 : ℝ) ^ k) ^ 2 := by
  have h1 : ((x : ℂ) + (y : ℂ) * Complex.I) = ((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I := by simp
  rw [h1, norm_div, div_pow, Complex.sq_norm, Complex.normSq_add_mul_I, norm_pow, Complex.norm_two]

lemma sum4 (P Q R : ℝ) :
    ∑ z : Qubits 2, (if z 0 then (if z 1 then P else Q) else (if z 1 then 0 else R)) = P + Q + R := by
  rw [← Equiv.sum_comp (piFinTwoEquiv fun _ => Bool).symm, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, piFinTwoEquiv, Equiv.coe_fn_symm_mk, Fin.cons_zero, Fin.cons_one,
    ite_true, ite_false, Bool.false_eq_true]
  ring

lemma normsq_vecV (k : ℕ) (φ : ℝ) (a b c d : ℤ) (z : Qubits 2) :
    ‖vecV k φ a b c d z‖ ^ 2 =
      (if z 0 then (if z 1 then ‖((c : ℂ) + (d : ℂ) * Complex.I) / (2 : ℂ) ^ k‖ ^ 2
        else ‖((a : ℂ) + (b : ℂ) * Complex.I) / (2 : ℂ) ^ k‖ ^ 2)
       else (if z 1 then 0 else ‖gammaApprox k φ‖ ^ 2)) := by
  unfold vecV
  rw [PiLp.toLp_apply]
  split_ifs <;> simp

end Aux_CliffordTApprox_Ancilla_four_square_unit_vector

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12 CliffordTApprox.Ancilla
  Aux_CliffordTApprox_Ancilla_four_square_unit_vector in
theorem solution (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    0 ≤ deficit k φ ∧
    (∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ) ∧
    ∀ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ →
      IsState (vecV k φ a b c d) := by
  have hpi := Real.pi_pos
  have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsin : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ₀ (by linarith)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hX0 : (0 : ℝ) ≤ (roundX k φ : ℝ) := by
    have : 0 ≤ roundX k φ := Int.floor_nonneg.mpr (mul_nonneg h2k.le hcos)
    exact_mod_cast this
  have hY0 : (0 : ℝ) ≤ (roundY k φ : ℝ) := by
    have : 0 ≤ roundY k φ := Int.floor_nonneg.mpr (mul_nonneg h2k.le hsin)
    exact_mod_cast this
  have hX1 : (roundX k φ : ℝ) ≤ 2 ^ k * Real.cos φ := Int.floor_le _
  have hY1 : (roundY k φ : ℝ) ≤ 2 ^ k * Real.sin φ := Int.floor_le _
  have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hcs := Real.cos_sq_add_sin_sq φ
  have hdefR : ((deficit k φ : ℤ) : ℝ) = (4 : ℝ) ^ k - (roundX k φ : ℝ) ^ 2 - (roundY k φ : ℝ) ^ 2 := by
    unfold deficit; push_cast; ring
  have hXs : (roundX k φ : ℝ) ^ 2 ≤ (2 ^ k * Real.cos φ) ^ 2 := pow_le_pow_left₀ hX0 hX1 2
  have hYs : (roundY k φ : ℝ) ^ 2 ≤ (2 ^ k * Real.sin φ) ^ 2 := pow_le_pow_left₀ hY0 hY1 2
  have h0 : 0 ≤ deficit k φ := by
    have : (0 : ℝ) ≤ ((deficit k φ : ℤ) : ℝ) := by
      rw [hdefR, h4]
      nlinarith
    exact_mod_cast this
  refine ⟨h0, ?_, ?_⟩
  · obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (deficit k φ).toNat
    refine ⟨a, b, c, d, ?_⟩
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h'
    rw [Int.toNat_of_nonneg h0] at h'
    linarith
  · intro a b c d h
    have hR : ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 + (d : ℝ) ^ 2) = ((deficit k φ : ℤ) : ℝ) := by
      exact_mod_cast h
    rw [hdefR] at hR
    unfold IsState
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    rw [Finset.sum_congr rfl (fun z _ => normsq_vecV k φ a b c d z), sum4]
    unfold gammaApprox
    rw [nsq, nsq, nsq, ← add_div, ← add_div, div_eq_one_iff_eq (by positivity), ← h4]
    linarith
