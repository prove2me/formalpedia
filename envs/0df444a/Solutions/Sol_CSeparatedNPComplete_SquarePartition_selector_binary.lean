-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.selector_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:46.701851+00:00
-- url     : https://prove2.me/submissions/0949a8f6-52bd-4a8e-99d4-89f143882735

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (b : ℕ → Bool) : is_binary (selector N b) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [selector, Fin.append_left]
    cases b j <;> simp
  · intro j
    simp only [selector, Fin.append_right]
    cases b j <;> simp
end CSeparatedNPComplete.SquarePartition
