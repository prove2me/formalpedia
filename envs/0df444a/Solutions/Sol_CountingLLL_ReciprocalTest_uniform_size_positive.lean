-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.uniform_size_positive
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:45:40.06399+00:00
-- url     : https://prove2.me/submissions/cef2baf7-d1d2-4d1c-8111-c918c065b827

import Definitions.Def_CountingLLL_ReciprocalTest

open CountingLLL.ReciprocalTest

private def Valid (s : State) : Prop := 0 < s.j ∨ s.phase = .start ∨ s.phase = .coinOracle .initial ∨ s.phase = .coinFair .initial ∨ s.phase = .done true

private theorem step_valid (ω : Entropy) (s : State) (hs : Valid s) : Valid (step ω s) := by
  cases hp : s.phase with
  | start => simp [step, hp, Valid]; split <;> simp
  | initialCheck => simp [Valid, hp] at hs; simp only [step, hp]; split <;> simp_all [Valid]
  | loop => simp [Valid, hp] at hs; simp only [step, hp]; split <;> simp_all [Valid]
  | coinOracle k =>
    cases k <;> simp only [step, hp] <;> split <;> simp_all [Valid, coinReturn] <;> omega
  | coinFair k =>
    cases k <;> simp only [step, hp] <;> split <;> simp_all [Valid, coinReturn] <;> omega
  | uniformCheck => simp [Valid, hp] at hs; simp only [step, hp]; split <;> simp_all [Valid]
  | done b => simp [step, hp]; exact hs

private theorem run_valid (ω : Entropy) (n : ℕ) : Valid (run ω n) := by
  induction n with
  | zero => simp [run, initial, Valid]
  | succ n ih =>
    rw [run, Function.iterate_succ_apply']
    exact step_valid ω (run ω n) ih

theorem solution (ω : Entropy) (n : ℕ) (h : (run ω n).phase = .uniformCheck) : 0 < (run ω n).j := by
  have := run_valid ω n
  simpa [Valid, h] using this
