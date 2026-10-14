-- Prove2me | solution 1 for ClassicalSecretary.neg_mul_log_max
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T15:53:10.393777+00:00
-- url     : https://prove2.me/submissions/91b5b73f-d4fd-400e-8f43-4cef59e6e6f2

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

set_option autoImplicit false

open Finset Filter Topology

namespace ClassicalSecretary.SecAnMax

/-- For `x > 0`, `-x log x ≤ e⁻¹`, with equality only at `x = e⁻¹`.
Proof: `log y ≤ y - 1` for `y = e⁻¹ / x`, strict unless `y = 1`. -/
theorem key (x : ℝ) (hx : 0 < x) :
    -x * Real.log x ≤ Real.exp (-1) ∧
      (-x * Real.log x = Real.exp (-1) → x = Real.exp (-1)) := by
  set y := Real.exp (-1) / x with hy
  have hypos : 0 < y := div_pos (Real.exp_pos _) hx
  have hlogy : Real.log y = -1 - Real.log x := by
    rw [hy, Real.log_div (Real.exp_pos _).ne' hx.ne', Real.log_exp]
  have hyx : y * x = Real.exp (-1) := by
    rw [hy]; field_simp
  constructor
  · have h1 := Real.log_le_sub_one_of_pos hypos
    rw [hlogy] at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 hx.le]
  · intro heq
    by_contra hne
    have hy1 : y ≠ 1 := by
      intro h1
      rw [h1, one_mul] at hyx
      exact hne hyx
    have h1 := Real.log_lt_sub_one_of_pos hypos hy1
    rw [hlogy] at h1
    nlinarith [mul_lt_mul_of_pos_left h1 hx]

end ClassicalSecretary.SecAnMax

open ClassicalSecretary in
theorem solution :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, -x * Real.log x ≤ Real.exp (-1)) ∧
    -Real.exp (-1) * Real.log (Real.exp (-1)) = Real.exp (-1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, -x * Real.log x = Real.exp (-1) → x = Real.exp (-1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      simp only [neg_zero, zero_mul]
      exact (Real.exp_pos _).le
    · exact (ClassicalSecretary.SecAnMax.key x h).1
  · rw [Real.log_exp]; ring
  · intro x hx heq
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      simp only [neg_zero, zero_mul] at heq
      exact absurd heq.symm (Real.exp_pos _).ne'
    · exact (ClassicalSecretary.SecAnMax.key x h).2 heq
