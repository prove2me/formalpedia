-- Prove2me | solution 1 for DeciSigma1.Automata.Semiautomaton.pathSafe_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:23.842792+00:00
-- url     : https://prove2.me/submissions/16d5d46f-3bb7-4911-9a22-57bcf7552dab

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
open DeciSigma1.Automata.Semiautomaton
variable {S : Type*}
namespace DeciSigma1.Automata.Semiautomaton
theorem _root_.solution (M : Semiautomaton α S) (G : S → Prop) (q : S) (w : Word α) :
    M.PathSafe G q w ↔ ∀ j ≤ w.length, G (runFrom M.step q (w.take j)) := by
  induction w generalizing q with
  | nil => simp [PathSafe, runFrom]
  | cons c w ih =>
    rw [PathSafe, ih]
    constructor
    · rintro ⟨hq, hw⟩ j hj
      cases j with
      | zero => exact hq
      | succ j => exact hw j (by simpa using hj)
    · intro h
      exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by simp; omega)⟩
end DeciSigma1.Automata.Semiautomaton
