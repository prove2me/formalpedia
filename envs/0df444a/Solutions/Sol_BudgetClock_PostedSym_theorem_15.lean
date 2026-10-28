-- Prove2me | solution 1 for BudgetClock.PostedSym.theorem_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:13:11.107744+00:00
-- url     : https://prove2.me/submissions/d300a451-b312-4029-bcf1-08501543444f

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting
import Theorems.Thm_BudgetClock_PostedSym_payment_bound
import Theorems.Thm_BudgetClock_PostedSym_case_1
import Theorems.Thm_BudgetClock_PostedSym_case_2

set_option autoImplicit false

open BudgetClock.PostedSym

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (v : Finset (Fin n) → ℝ), IsSymmetricSubmodular n v →
      ∀ (B : ℝ), 0 < B →
      ∀ (c : Fin n → ℝ), (∀ i, 0 ≤ c i) → (∀ i, c i ≤ B) →
      ∀ (j : Fin n),
        (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i ≤ B) ∧
        ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
          v O ≤ C * Real.log n * v (mech5 n B c j).1 := by
  refine ⟨5, by norm_num, ?_⟩
  intro n hn v hv B hB c hc0 hcB j
  refine ⟨(payment_bound n hn B hB c hc0 hcB j).2, ?_⟩
  intro O hO
  have hlog2 : (2 : ℝ) / 3 < Real.log n := by
    have h2 := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  have hvW : 0 ≤ v (mech5 n B c j).1 := by
    obtain ⟨r, hr0, _, hvr⟩ := hv
    rw [hvr]
    refine Finset.sum_nonneg (fun k hk => hr0 k ?_)
    have := Finset.card_le_univ (mech5 n B c j).1
    simp at hk this
    omega
  rcases Nat.eq_zero_or_pos (scan n B c j).count with h0 | h1
  · have h := (case_1 n hn v hv B hB c hc0 hcB j h0).2 O hO
    calc v O ≤ (2 * Real.log n + 1) * v (mech5 n B c j).1 := h
      _ ≤ 5 * Real.log n * v (mech5 n B c j).1 :=
        mul_le_mul_of_nonneg_right (by linarith) hvW
  · have h := case_2 n hn v hv B hB c hc0 hcB j h1 O hO
    calc v O ≤ (2 * Real.log n + 2) * v (mech5 n B c j).1 := h
      _ ≤ 5 * Real.log n * v (mech5 n B c j).1 :=
        mul_le_mul_of_nonneg_right (by linarith) hvW
