-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_form_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:21.971912+00:00
-- url     : https://prove2.me/submissions/85767c86-15ce-460c-991a-bb09fe5dc9e1

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Theorems.Thm_CSeparatedNPComplete_hinge_against_app

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (c : ℝ) (a : Vec n)
    (L : List (Gaussian n)) (g : Gaussian n) :
    hinge_form c a (L ++ [g]) = hinge_form c a L + hinge_to c a L g := by
  induction L with
  | nil => simp [hinge_form, hinge_against, hinge_to]
  | cons h L ih =>
    simp only [List.cons_append, hinge_form, hinge_against_app, hinge_against, add_zero]
    rw [ih]
    simp only [hinge_to, List.map_cons, List.sum_cons]
    ring
end CSeparatedNPComplete
