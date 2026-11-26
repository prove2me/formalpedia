-- Prove2me | solution 1 for BrooksTheorem.Aux.sq_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:10.086065+00:00
-- url     : https://prove2.me/submissions/10b6ec4a-2de5-415b-a563-99216cb68f29

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
include h2 h01
namespace BrooksTheorem.Aux
theorem _root_.solution (n : ℕ) : G.Adj (sq G v0 v1 n) (sq G v0 v1 (n + 1)) := by
  rcases n with _ | n
  · exact h01
  · rw [sq_add_two G]; exact (other_spec G h2 _ _).1
end BrooksTheorem.Aux
