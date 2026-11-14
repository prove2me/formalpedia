-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_stopping_transition
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:15:11.9362+00:00
-- url     : https://prove2.me/submissions/0be78dab-4b73-44e8-8be1-a260a93ba6bf

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_stopping_fresh
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

private theorem sim_step (ω : Entropy) (s : State) (S : Finset ReadIndex) :
    (CountingLLL.RevealMachine.step suppressedRevealProgram (entropyCode ω) (s,S)).1 = allSuppressedStep ω s := by
  cases hs : s.phase <;> simp [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex,
    allSuppressedStep, suppressedStep, CountingLLL.ReciprocalTest.step, hs, entropyCode, uniformEntropy]
  all_goals split <;> simp_all


/-- The same transition law holds at any finite history-adapted stopping time. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val)) (s s' : State) :
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s} * suppressedTransitionMass B s s' := by
  classical
  have hn (ω : Entropy) (n : ℕ) : allSuppressedRun ω (n+1) = allSuppressedStep ω (allSuppressedRun ω n) := by
    simp [allSuppressedRun, Function.iterate_succ_apply']
  cases ha : readIndex s with
  | some a =>
    let U : Set ℕ := {v | allSuppressedStep (uniformEntropy v) s = s'}
    have h := suppressed_stopping_fresh B hB T H hT s a ha U
    have heq : {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
        {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have hstep : allSuppressedStep ω s = allSuppressedStep (uniformEntropy (entropyCode ω a)) s := by
        have hh := sim_step ω s (∅ : Finset ReadIndex)
        simp [CountingLLL.RevealMachine.step, suppressedRevealProgram, ha] at hh
        exact hh.symm
      constructor
      · rintro ⟨n,ht,hs,hnext⟩
        refine ⟨n,ht,hs, ?_⟩
        change allSuppressedStep (uniformEntropy (entropyCode ω a)) s = s'
        rw [← hstep, ← hs, ← hn]
        exact hnext
      · rintro ⟨n,ht,hs,hnext⟩
        refine ⟨n,ht,hs, ?_⟩
        change allSuppressedStep (uniformEntropy (entropyCode ω a)) s = s' at hnext
        rw [hn, hs, hstep]
        exact hnext
    rw [heq]
    simpa [suppressedTransitionMass, ha, U] using h
  | none =>
    have hstep (ω : Entropy) : allSuppressedStep ω s = allSuppressedStep (uniformEntropy 0) s := by
      have hh := sim_step ω s (∅ : Finset ReadIndex)
      simp [CountingLLL.RevealMachine.step, suppressedRevealProgram, ha] at hh
      exact hh.symm
    by_cases he : allSuppressedStep (uniformEntropy 0) s = s'
    · have heq : {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
          {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨n,ht,hs,hnext⟩; exact ⟨n,ht,hs⟩
        · rintro ⟨n,ht,hs⟩; refine ⟨n,ht,hs,?_⟩; rw [hn,hs,hstep,he]
      simp [suppressedTransitionMass, ha, he, heq]
    · have heq : {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
        rintro n ⟨ht,hs,hnext⟩
        rw [hn,hs,hstep] at hnext
        exact he hnext
      simp [suppressedTransitionMass, ha, he, heq]
