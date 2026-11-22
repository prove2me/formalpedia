-- Prove2me | solution 1 for DeciSigma1.runFrom_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:25.677344+00:00
-- url     : https://prove2.me/submissions/52db33cd-0b2b-4543-88eb-dd47e8f16bb7

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {α S : Type*}
namespace DeciSigma1
theorem _root_.solution (δ : S → α → S) (q : S) (u v : List α) :
    runFrom δ q (u ++ v) = runFrom δ (runFrom δ q u) v := List.foldl_append
end DeciSigma1
