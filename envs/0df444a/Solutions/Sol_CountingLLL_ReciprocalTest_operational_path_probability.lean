-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_path_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:39:11.153338+00:00
-- url     : https://prove2.me/submissions/65a92586-f481-4f40-82ed-fe1366daa975

import Theorems.Thm_CountingLLL_ReciprocalTest_operational_history_transition
import Theorems.Thm_CountingLLL_ReciprocalTest_entropy_is_probability
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal BigOperators
open Classical

/-- Exact cylinder probabilities of the operational state trajectory. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (x : ℕ → State) (n : ℕ) :
    entropyLaw B {ω | ∀ j ≤ n, run ω j = x j} =
      (if x 0 = initial then 1 else 0) * ∏ j ∈ Finset.range n, transitionMass B (x j) (x (j+1)) := by
  classical
  induction n with
  | zero =>
    have hprob : IsProbabilityMeasure (entropyLaw B) := by
      exact entropy_is_probability B hB
    letI : IsProbabilityMeasure (entropyLaw B) := hprob
    by_cases h : x 0 = initial
    · simp [h, run]
    · simp [h, Ne.symm h, run]
  | succ n ih =>
    let H : (Fin (n+1) → State) → Prop := fun f => ∀ j : Fin (n+1), f j = x j.val
    have ht := operational_history_transition B hB n H (x n) (x (n+1))
    have he0 : {ω | H (fun j => run ω j.val) ∧ run ω n = x n} =
        {ω | ∀ j ≤ n, run ω j = x j} := by
      ext ω
      simp only [Set.mem_setOf_eq, H]
      constructor
      · rintro ⟨h,hn⟩ j hj
        exact h ⟨j, by omega⟩
      · intro h
        exact ⟨fun j => h j.val (by omega), h n (by omega)⟩
    have he1 : {ω | H (fun j => run ω j.val) ∧ run ω n = x n ∧ run ω (n+1) = x (n+1)} =
        {ω | ∀ j ≤ n+1, run ω j = x j} := by
      ext ω
      simp only [Set.mem_setOf_eq, H]
      constructor
      · rintro ⟨h,hn,hs⟩ j hj
        by_cases hnj : j ≤ n
        · exact h ⟨j, by omega⟩
        · have : j = n+1 := by omega
          simpa [this] using hs
      · intro h
        exact ⟨fun j => h j.val (by omega), h n (by omega), h (n+1) (by omega)⟩
    rw [he1,he0,ih] at ht
    simpa [Finset.prod_range_succ, mul_assoc] using ht
