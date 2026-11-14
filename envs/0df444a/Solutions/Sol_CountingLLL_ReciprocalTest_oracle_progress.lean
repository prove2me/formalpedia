-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.oracle_progress
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:27:02.849285+00:00
-- url     : https://prove2.me/submissions/2db89939-8d6a-4369-9edc-48e237b7da62

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private def rank (p : Phase) : ℕ := match p with
  | .start => 1 | .initialCheck => 2 | .loop => 1
  | .coinOracle _ => 0 | .coinFair _ => 3 | .uniformCheck => 2 | .done _ => 0

private def Live (s : State) : Prop := s.phase ≠ .done false ∧ s.phase ≠ .done true

private theorem step_potential (ω : Entropy) (s : State) (hn : Live (step ω s)) :
    1 + rank (step ω s).phase + 4*s.oracleUsed ≤ rank s.phase + 4*(step ω s).oracleUsed := by
  cases hp : s.phase with
  | start =>
    simp only [step, hp] at hn ⊢
    split <;> simp_all [rank, Live]
  | initialCheck =>
    simp only [step, hp] at hn ⊢
    split <;> simp_all [rank, Live]
  | loop =>
    simp only [step, hp] at hn ⊢
    split <;> simp_all [rank, Live]
  | coinOracle k =>
    cases k <;> simp only [step, hp] at hn ⊢ <;> split <;> simp_all [rank, Live, coinReturn] <;> omega
  | coinFair k =>
    cases k <;> simp only [step, hp] at hn ⊢ <;> split <;> simp_all [rank, Live, coinReturn] <;> omega
  | uniformCheck =>
    simp only [step, hp] at hn ⊢
    split <;> simp_all [rank, Live]
  | done b => cases b <;> simp_all [step, Live]

theorem solution (ω : Entropy) (n : ℕ)
    (hlive : (run ω n).phase ≠ .done false ∧ (run ω n).phase ≠ .done true) :
    n ≤ 4*(run ω n).oracleUsed+1 := by
  have hpot : ∀ n, Live (run ω n) → n + rank (run ω n).phase ≤ 4*(run ω n).oracleUsed+1 := by
    intro n
    induction n with
    | zero => intro h; simp [run, initial, rank]
    | succ n ih =>
      intro hl
      have hrs : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
      have hl' : Live (step ω (run ω n)) := by simpa [hrs] using hl
      have hp := step_potential ω (run ω n) hl'
      have hprev : Live (run ω n) := by
        rcases hl with ⟨h0,h1⟩
        constructor
        · intro hdone
          have hfix : step ω (run ω n) = run ω n := by simp [step, hdone]
          exact h0 (by simpa [hrs,hfix] using hdone)
        · intro hdone
          have hfix : step ω (run ω n) = run ω n := by simp [step, hdone]
          exact h1 (by simpa [hrs,hfix] using hdone)
      have hi := ih hprev
      rw [hrs] at hl
      rw [hrs]
      omega
  have h := hpot n hlive
  omega
