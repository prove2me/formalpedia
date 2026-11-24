-- Prove2me | solution 1 for BalanceSpecification.length_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:24.529608+00:00
-- url     : https://prove2.me/submissions/0093325c-c9b6-4be3-9e80-ce6caa0ac9c7

module
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Language

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {A : Type*} (x : Configuration A) (k : ℤ) (n : ℕ) :
    (block x k n).length = n := List.length_ofFn
end BalanceSpecification
