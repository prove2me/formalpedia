-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.reciprocal_reveal_simulates
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:52:58.306111+00:00
-- url     : https://prove2.me/submissions/e1b0aac3-6215-4e61-aef2-711859630709

import Definitions.Def_CountingLLL_ReciprocalReveal
set_option autoImplicit false
open CountingLLL.ReciprocalTest CountingLLL.RevealMachine

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

theorem solution (ω : Entropy) (n : ℕ) :
    (CountingLLL.RevealMachine.run revealProgram (entropyCode ω) initial n).1 =
      CountingLLL.ReciprocalTest.run ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hr : CountingLLL.RevealMachine.run revealProgram (entropyCode ω) initial (n+1) =
        CountingLLL.RevealMachine.step revealProgram (entropyCode ω)
          (CountingLLL.RevealMachine.run revealProgram (entropyCode ω) initial n) := by
      simp [CountingLLL.RevealMachine.run, Function.iterate_succ_apply']
    have hc : CountingLLL.ReciprocalTest.run ω (n+1) = step ω (CountingLLL.ReciprocalTest.run ω n) := by
      simp [CountingLLL.ReciprocalTest.run, Function.iterate_succ_apply']
    rw [hr, hc, ← ih]
    exact sim_step ω _ _
