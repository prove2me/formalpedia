-- Prove2me | solution 1 for Freiman.continuant_fibonacci_pair
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:26:52.765544+00:00
-- url     : https://prove2.me/submissions/979fb6bf-2cae-485c-9c74-7454f7c0712c

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_continuant_append

open Freiman

theorem solution (w : List ℕ+) :
    Nat.fib w.length ≤ wordContinuantPrevQ w ∧ Nat.fib (w.length+1) ≤ wordContinuantQ w := by
  induction w using List.reverseRecOn with
  | nil => norm_num [wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
  | append_singleton w a ih =>
    have hq : wordContinuantQ (w ++ [a]) = (a:ℕ)*wordContinuantQ w+wordContinuantPrevQ w :=
      congrArg (fun d : (ℕ×ℕ)×(ℕ×ℕ) => d.2.2) (continuant_append w a)
    have hp : wordContinuantPrevQ (w ++ [a]) = wordContinuantQ w :=
      congrArg (fun d : (ℕ×ℕ)×(ℕ×ℕ) => d.2.1) (continuant_append w a)
    simp only [List.length_append, List.length_singleton, hp, hq]
    refine ⟨ih.2, ?_⟩
    rw [show w.length+1+1=w.length+2 by omega, Nat.fib_add_two]
    have ha := a.pos
    nlinarith [ih.1, ih.2]
