-- Prove2me | solution 1 for BudgetClock.Subadditive.value_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:33:49.663762+00:00
-- url     : https://prove2.me/submissions/ae33741f-a460-4c0e-82ac-d38fe2551a77

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Mechanism

set_option autoImplicit false
open BudgetClock.Subadditive

lemma better_ge_left {n : ℕ} (v : Finset (Fin n) → ℝ) (S₁ S₂ : Finset (Fin n)) :
    v S₁ ≤ v (better v S₁ S₂) := by
  unfold better
  split_ifs with h
  · exact h.le
  · exact le_rfl

lemma better_ge_right {n : ℕ} (v : Finset (Fin n) → ℝ) (S₁ S₂ : Finset (Fin n)) :
    v S₂ ≤ v (better v S₁ S₂) := by
  unfold better
  split_ifs with h
  · exact le_rfl
  · exact not_lt.1 h

lemma run_step_mono {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (F : ℕ) :
    ∀ s : State n, v (better v (run v c B alg F s).Sprev (run v c B alg F s).Scurr) ≤
      v (better v (run v c B alg (F + 1) s).Sprev (run v c B alg (F + 1) s).Scurr) := by
  induction F with
  | zero =>
    intro s
    simp only [run]
    split_ifs with h
    · have h1 : (phase v c B alg s).Sprev = better v s.Sprev s.Scurr := rfl
      calc v (better v s.Sprev s.Scurr) = v (phase v c B alg s).Sprev := by rw [h1]
        _ ≤ _ := better_ge_left v _ _
    · exact le_rfl
  | succ F ih =>
    intro s
    by_cases h : (s.A \ (s.Sprev ∪ s.Scurr)).Nonempty
    · have e1 : run v c B alg (F + 1) s = run v c B alg F (phase v c B alg s) := by
        simp only [run, if_pos h]
      have e2 : run v c B alg (F + 1 + 1) s = run v c B alg (F + 1) (phase v c B alg s) := by
        simp only [run, if_pos h]
      rw [e1, e2]
      exact ih _
    · have e1 : run v c B alg (F + 1) s = s := by simp only [run, if_neg h]
      have e2 : run v c B alg (F + 1 + 1) s = s := by simp only [run, if_neg h]
      rw [e1, e2]

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (F F' : ℕ) (hFF' : F ≤ F') :
    v (mechanism4 v c B alg F).1 ≤ v (mechanism4 v c B alg F').1 := by
  have key : Monotone (fun F => v (mechanism4 v c B alg F).1) := by
    apply monotone_nat_of_le_succ
    intro F
    exact run_step_mono v c B alg F _
  exact key hFF'

