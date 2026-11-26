-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_against_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:54.177551+00:00
-- url     : https://prove2.me/submissions/f9ce977a-0da5-4322-a929-e0ae30043298

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Theorems.Thm_CSeparatedNPComplete_gaussian_pair_hinge_nonneg

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L : List (Gaussian n)) : 0 ≤ hinge_against c a g L := by
  induction L with
  | nil => exact le_rfl
  | cons h L ih => exact add_nonneg (gaussian_pair_hinge_nonneg c a g h) ih
end CSeparatedNPComplete
