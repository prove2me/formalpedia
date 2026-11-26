-- Prove2me | solution 1 for BrooksTheorem.Aux.sq_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:51.352559+00:00
-- url     : https://prove2.me/submissions/1867da23-1ef0-4239-93d3-235d4ff77245

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (v0 v1 : V) (h01 : G.Adj v0 v1)
namespace BrooksTheorem.Aux
theorem _root_.solution (n : ℕ) :
    sq G v0 v1 (n + 2) = other G (sq G v0 v1 (n + 1)) (sq G v0 v1 n) := rfl
end BrooksTheorem.Aux
