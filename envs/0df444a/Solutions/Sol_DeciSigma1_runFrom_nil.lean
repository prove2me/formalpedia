-- Prove2me | solution 1 for DeciSigma1.runFrom_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:19.349253+00:00
-- url     : https://prove2.me/submissions/c2777615-7b9b-4580-98c0-d54b821f56d8

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
theorem _root_.solution (δ : S → α → S) (q : S) : runFrom δ q [] = q := rfl
end DeciSigma1
