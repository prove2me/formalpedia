-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_history_transition
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:35:59.747205+00:00
-- url     : https://prove2.me/submissions/246a7e52-12f1-46ce-86d2-83728b5a8e54

import Definitions.Def_CountingLLL_ReciprocalTransition
import Theorems.Thm_CountingLLL_ReciprocalTest_operational_history_fresh
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

private theorem sim_step (ω : Entropy) (s : State) (S : Finset ReadIndex) :
    (CountingLLL.RevealMachine.step revealProgram (entropyCode ω) (s,S)).1 = step ω s := by
  cases hs : s.phase <;> simp only [CountingLLL.RevealMachine.step, revealProgram, readIndex, hs]
  all_goals try simp only [Prod.fst]
  all_goals simp [CountingLLL.ReciprocalTest.step, hs, entropyCode, uniformEntropy]
  have hh := (ω.2.2 (s.j-1,s.uniformUsed)).isLt
  rw [Nat.mod_eq_of_lt hh]
  have hz : (ω.2.2 (s.j-1,s.uniformUsed)).val = 0 ↔ ω.2.2 (s.j-1,s.uniformUsed) = 0 := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  by_cases hzero : (ω.2.2 (s.j-1,s.uniformUsed)).val = 0
  · have hz' := hz.mp hzero
    simp [hzero, hz']
  · have hne : ω.2.2 (s.j-1,s.uniformUsed) ≠ 0 := fun h => hzero (hz.mpr h)
    simp [hzero, hne]



/-- The operational transition kernel remains valid after conditioning on an arbitrary past history. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s s' : State) :
    entropyLaw B {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
      CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
    entropyLaw B {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
      CountingLLL.ReciprocalTest.run ω n = s} * transitionMass B s s' := by
  classical
  have hn (ω : Entropy) : CountingLLL.ReciprocalTest.run ω (n+1) = step ω (CountingLLL.ReciprocalTest.run ω n) := by
    simp [CountingLLL.ReciprocalTest.run, Function.iterate_succ_apply']
  cases ha : readIndex s with
  | some a =>
    let U : Set ℕ := {v | step (uniformEntropy v) s = s'}
    have h := operational_history_fresh B hB n s a ha H U
    have heq : {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
        CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
        {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
        CountingLLL.ReciprocalTest.run ω n = s ∧ entropyCode ω a ∈ U} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have hstep : step ω s = step (uniformEntropy (entropyCode ω a)) s := by
        have hh := sim_step ω s (∅ : Finset ReadIndex)
        simp [CountingLLL.RevealMachine.step, revealProgram, ha] at hh
        exact hh.symm
      rw [hn ω]
      constructor
      · rintro ⟨hh,hs,hnext⟩
        refine ⟨hh,hs, ?_⟩
        change step (uniformEntropy (entropyCode ω a)) s = s'
        rw [← hstep, ← hs]
        exact hnext
      · rintro ⟨hh,hs,hnext⟩
        refine ⟨hh,hs, ?_⟩
        change step (uniformEntropy (entropyCode ω a)) s = s' at hnext
        rw [hs, hstep]
        exact hnext
    rw [heq]
    simpa [transitionMass, ha, U] using h
  | none =>
    have hstep (ω : Entropy) : step ω s = step (uniformEntropy 0) s := by
      have hh := sim_step ω s (∅ : Finset ReadIndex)
      simp [CountingLLL.RevealMachine.step, revealProgram, ha] at hh
      exact hh.symm
    by_cases he : step (uniformEntropy 0) s = s'
    · have heq : {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
          CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
          {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧ CountingLLL.ReciprocalTest.run ω n = s} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hh,hs,ht⟩; exact ⟨hh,hs⟩
        · rintro ⟨hh,hs⟩; refine ⟨hh,hs,?_⟩; rw [hn,hs,hstep,he]
      simp [transitionMass, ha, he, heq]
    · have heq : {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
          CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hh,hs,ht⟩
        rw [hn,hs,hstep] at ht
        exact he ht
      simp [transitionMass, ha, he, heq]
