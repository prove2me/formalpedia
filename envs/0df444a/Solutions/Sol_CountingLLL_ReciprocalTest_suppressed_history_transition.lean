-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_history_transition
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:03.000737+00:00
-- url     : https://prove2.me/submissions/12e2c1ca-80a9-4275-b8c5-f91ffa711c47

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_history_fresh
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

private theorem sim_step (ω : Entropy) (s : State) (S : Finset ReadIndex) :
    (CountingLLL.RevealMachine.step suppressedRevealProgram (entropyCode ω) (s,S)).1 = allSuppressedStep ω s := by
  cases hs : s.phase <;> simp [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex,
    allSuppressedStep, suppressedStep, CountingLLL.ReciprocalTest.step, hs, entropyCode, uniformEntropy]
  all_goals split <;> simp_all

/-- The operational transition kernel remains valid after conditioning on an arbitrary past history. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s s' : State) :
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s} * suppressedTransitionMass B s s' := by
  classical
  have hn (ω : Entropy) : allSuppressedRun ω (n+1) = allSuppressedStep ω (allSuppressedRun ω n) := by
    simp [allSuppressedRun, Function.iterate_succ_apply']
  cases ha : readIndex s with
  | some a =>
    let U : Set ℕ := {v | allSuppressedStep (uniformEntropy v) s = s'}
    have h := suppressed_history_fresh B hB n s a ha H U
    have heq : {ω | H (fun j => allSuppressedRun ω j.val) ∧
        allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
        {ω | H (fun j => allSuppressedRun ω j.val) ∧
        allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have hstep : allSuppressedStep ω s = allSuppressedStep (uniformEntropy (entropyCode ω a)) s := by
        have hh := sim_step ω s (∅ : Finset ReadIndex)
        simp [CountingLLL.RevealMachine.step, suppressedRevealProgram, ha] at hh
        exact hh.symm
      rw [hn ω]
      constructor
      · rintro ⟨hh,hs,hnext⟩
        refine ⟨hh,hs, ?_⟩
        change allSuppressedStep (uniformEntropy (entropyCode ω a)) s = s'
        rw [← hstep, ← hs]
        exact hnext
      · rintro ⟨hh,hs,hnext⟩
        refine ⟨hh,hs, ?_⟩
        change allSuppressedStep (uniformEntropy (entropyCode ω a)) s = s' at hnext
        rw [hs, hstep]
        exact hnext
    rw [heq]
    simpa [suppressedTransitionMass, ha, U] using h
  | none =>
    have hstep (ω : Entropy) : allSuppressedStep ω s = allSuppressedStep (uniformEntropy 0) s := by
      have hh := sim_step ω s (∅ : Finset ReadIndex)
      simp [CountingLLL.RevealMachine.step, suppressedRevealProgram, ha] at hh
      exact hh.symm
    by_cases he : allSuppressedStep (uniformEntropy 0) s = s'
    · have heq : {ω | H (fun j => allSuppressedRun ω j.val) ∧
          allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
          {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hh,hs,ht⟩; exact ⟨hh,hs⟩
        · rintro ⟨hh,hs⟩; refine ⟨hh,hs,?_⟩; rw [hn,hs,hstep,he]
      simp [suppressedTransitionMass, ha, he, heq]
    · have heq : {ω | H (fun j => allSuppressedRun ω j.val) ∧
          allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hh,hs,ht⟩
        rw [hn,hs,hstep] at ht
        exact he ht
      simp [suppressedTransitionMass, ha, he, heq]
