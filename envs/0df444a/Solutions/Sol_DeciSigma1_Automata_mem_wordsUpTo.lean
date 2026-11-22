-- Prove2me | solution 1 for DeciSigma1.Automata.mem_wordsUpTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:21.751801+00:00
-- url     : https://prove2.me/submissions/acc4c743-4328-47f9-8c4d-863ad670cfec

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_snoc

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Automata
variable {α : Type*}
namespace DeciSigma1.Automata
theorem _root_.solution [Fintype α] [DecidableEq α] (w : Word α) (n : ℕ) :
    w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons c w => simp [wordsUpTo, ih]
end DeciSigma1.Automata
