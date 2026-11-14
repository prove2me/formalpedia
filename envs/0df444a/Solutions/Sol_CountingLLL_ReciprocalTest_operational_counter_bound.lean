-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_counter_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:33:05.131532+00:00
-- url     : https://prove2.me/submissions/2ff757f0-0945-4a66-9f7c-01116c2523e5

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private theorem coin_bound (k : Context) (v : Bool) (s : State) (h : s.i ≤ 2*s.j) :
    (coinReturn k v s).i ≤ 2*(coinReturn k v s).j := by
  cases k <;> cases v <;> simp [coinReturn] <;> omega

private theorem step_bound (ω : Entropy) (s : State) (h : s.i ≤ 2*s.j) :
    (step ω s).i ≤ 2*(step ω s).j := by
  cases hp : s.phase <;> simp only [step, hp]
  all_goals try split
  all_goals try apply coin_bound
  all_goals simp_all
  all_goals omega

theorem solution (ω : Entropy) (n : ℕ) :
    (run ω n).i ≤ 2 * (run ω n).j := by
  induction n with
  | zero => simp [run, initial]
  | succ n ih =>
    rw [run, Function.iterate_succ_apply']
    exact step_bound ω (run ω n) ih

