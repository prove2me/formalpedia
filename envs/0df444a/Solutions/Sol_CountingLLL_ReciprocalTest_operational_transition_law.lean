-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_transition_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:14:25.956201+00:00
-- url     : https://prove2.me/submissions/48f23096-ec86-4232-bd9e-5412ce6d32a0

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_operational_query_fresh
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


/-- The one-step joint transition law of the original operational machine. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (s s' : State) (a : ReadIndex) (ha : readIndex s = some a) :
    entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s} *
        readLaw B a {v | step (uniformEntropy v) s = s'} := by
  let U : Set ℕ := {v | step (uniformEntropy v) s = s'}
  have h := operational_query_fresh B hB n s a ha U
  have heq : {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
      {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ entropyCode ω a ∈ U} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hstep : step ω s = step (uniformEntropy (entropyCode ω a)) s := by
      have hh := sim_step ω s (∅ : Finset ReadIndex)
      simp [CountingLLL.RevealMachine.step, revealProgram, ha] at hh
      exact hh.symm
    have hn : CountingLLL.ReciprocalTest.run ω (n+1) = step ω (CountingLLL.ReciprocalTest.run ω n) := by
      simp [CountingLLL.ReciprocalTest.run, Function.iterate_succ_apply']
    rw [hn]
    constructor
    · rintro ⟨hs,hnext⟩
      refine ⟨hs, ?_⟩
      change step (uniformEntropy (entropyCode ω a)) s = s'
      rw [← hstep, ← hs]
      exact hnext
    · rintro ⟨hs,hnext⟩
      refine ⟨hs, ?_⟩
      change step (uniformEntropy (entropyCode ω a)) s = s' at hnext
      rw [hs, hstep]
      exact hnext
  rw [heq]
  exact h

