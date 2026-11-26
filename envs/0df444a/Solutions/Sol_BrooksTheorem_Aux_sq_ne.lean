-- Prove2me | solution 1 for BrooksTheorem.Aux.sq_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:15.537687+00:00
-- url     : https://prove2.me/submissions/6d59a3bf-91cb-4386-9606-8b6ce381f27d

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle
public import Theorems.Thm_BrooksTheorem_Aux_other_spec
public import Theorems.Thm_BrooksTheorem_Aux_sq_add_two

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (v0 v1 : V) (h01 : G.Adj v0 v1)
include h2
namespace BrooksTheorem.Aux
theorem _root_.solution (n : ℕ) : sq G v0 v1 (n + 2) ≠ sq G v0 v1 n := by
  rw [sq_add_two G]; exact (other_spec G h2 _ _).2
end BrooksTheorem.Aux
