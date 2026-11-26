-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_form_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:30.149931+00:00
-- url     : https://prove2.me/submissions/e5ef8aee-56a8-405e-863c-dfeab07c6c38

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Theorems.Thm_CSeparatedNPComplete_hinge_against_nonneg

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (c : ℝ) (a : Vec n) (L : List (Gaussian n)) :
    0 ≤ hinge_form c a L := by
  induction L with
  | nil => exact le_rfl
  | cons g L ih => exact add_nonneg (hinge_against_nonneg c a g L) ih
end CSeparatedNPComplete
