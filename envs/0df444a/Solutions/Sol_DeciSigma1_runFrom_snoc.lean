-- Prove2me | solution 1 for DeciSigma1.runFrom_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:53.058805+00:00
-- url     : https://prove2.me/submissions/55879039-8554-415b-bf27-13613926f245

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Theorems.Thm_DeciSigma1_runFrom_append

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {α S : Type*}
namespace DeciSigma1
theorem _root_.solution (δ : S → α → S) (q : S) (u : List α) (c : α) :
    runFrom δ q (u ++ [c]) = δ (runFrom δ q u) c := by
  rw [runFrom_append]; rfl
end DeciSigma1
