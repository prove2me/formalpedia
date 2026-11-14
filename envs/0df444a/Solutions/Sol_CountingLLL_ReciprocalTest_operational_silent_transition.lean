-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_silent_transition
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:12:01.725073+00:00
-- url     : https://prove2.me/submissions/d785920d-ef05-4c74-80ca-e31e602374b8

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw

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


/-- Silent operational phases have deterministic next state. -/
theorem solution (B : ℝ≥0∞) (n : ℕ) (s s' : State)
    (ha : readIndex s = none) :
    (step (uniformEntropy 0) s = s' →
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
        entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s}) ∧
    (step (uniformEntropy 0) s ≠ s' →
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} = 0) := by
  have hstep (ω : Entropy) : step ω s = step (uniformEntropy 0) s := by
    have hh := sim_step ω s (∅ : Finset ReadIndex)
    simp [CountingLLL.RevealMachine.step, revealProgram, ha] at hh
    exact hh.symm
  constructor
  · intro hnext
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    have hn : CountingLLL.ReciprocalTest.run ω (n+1) = step ω (CountingLLL.ReciprocalTest.run ω n) := by
      simp [CountingLLL.ReciprocalTest.run, Function.iterate_succ_apply']
    rw [hn]
    constructor
    · exact And.left
    · intro hs
      refine ⟨hs, ?_⟩
      rw [hs, hstep, hnext]
  · intro hnext
    have hempty : {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hs hn
      have hr : CountingLLL.ReciprocalTest.run ω (n+1) = step ω (CountingLLL.ReciprocalTest.run ω n) := by
        simp [CountingLLL.ReciprocalTest.run, Function.iterate_succ_apply']
      rw [hr, hs, hstep] at hn
      exact hnext hn
    rw [hempty, measure_empty]
