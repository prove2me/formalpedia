-- Prove2me | solution 1 for ErdosGirth.sum_wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:04.862799+00:00
-- url     : https://prove2.me/submissions/01a180b3-f88f-41aa-92d9-002eacccd68a

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (m : ℕ) (p : ℝ) : ∑ S ∈ (pairs m).powerset, wt m p S = 1 := by
  have := Finset.prod_add (fun _ => p) (fun _ => 1 - p) (pairs m)
  simp only [add_sub_cancel, prod_const_one] at this
  exact this.symm
end ErdosGirth
