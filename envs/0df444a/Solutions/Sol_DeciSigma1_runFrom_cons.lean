-- Prove2me | solution 1 for DeciSigma1.runFrom_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:20.04312+00:00
-- url     : https://prove2.me/submissions/eebdada1-466c-4c35-9e6a-818e4fae4ddb

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
theorem _root_.solution (δ : S → α → S) (q : S) (c : α) (w : List α) :
    runFrom δ q (c :: w) = runFrom δ (δ q c) w := rfl
end DeciSigma1
