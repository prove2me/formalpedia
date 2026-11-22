-- Prove2me | solution 1 for DeciSigma1.Automata.Semiautomaton.pathSafe_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:40:29.948119+00:00
-- url     : https://prove2.me/submissions/19c8e749-bb3c-4890-ae91-b36b965ef9c6

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Theorems.Thm_DeciSigma1_Automata_Semiautomaton_pathSafe_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Automata
variable {α : Type*}
open DeciSigma1.Automata.Semiautomaton
variable {S : Type*}
namespace DeciSigma1.Automata.Semiautomaton
theorem _root_.solution (M : Semiautomaton α S) (G : S → Prop) (q : S) (u v : Word α) :
    M.PathSafe G q (u ++ v) ↔
      M.PathSafe G q u ∧ M.PathSafe G (runFrom M.step q u) v := by
  induction u generalizing q with
  | nil =>
    change M.PathSafe G q v ↔ G q ∧ M.PathSafe G q v
    exact ⟨fun h => ⟨(pathSafe_iff M G q v).mp h 0 (by omega), h⟩, And.right⟩
  | cons c u ih =>
    change (G q ∧ M.PathSafe G (M.step q c) (u ++ v)) ↔
      (G q ∧ M.PathSafe G (M.step q c) u) ∧ M.PathSafe G (runFrom M.step (M.step q c) u) v
    rw [ih, and_assoc]
end DeciSigma1.Automata.Semiautomaton
