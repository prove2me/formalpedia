-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_form_app_no_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:10.804435+00:00
-- url     : https://prove2.me/submissions/2b511a79-515d-46ca-9e33-eec4d841ee85

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
    (L₁ L₂ : List (Gaussian n)) (h : ∀ g ∈ L₁, hinge_against c a g L₂ = 0) :
    hinge_form c a (L₁ ++ L₂) = hinge_form c a L₁ + hinge_form c a L₂ := by
  induction L₁ with
  | nil => simp [hinge_form]
  | cons g L ih =>
    simp only [List.cons_append, hinge_form, hinge_against_app, h g (by simp), add_zero]
    rw [ih (fun g hg => h g (by simp [hg]))]
    ring
end CSeparatedNPComplete
