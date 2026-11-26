-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.right_as_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:32.880934+00:00
-- url     : https://prove2.me/submissions/09fb9401-a838-41c8-9b8f-2fead36ea8e5

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    rightSum N m a K b = leftSum N m a K (fun i => !(b i)) := by
  apply Finset.sum_congr rfl
  intro i _
  cases hb : b i <;> simp [hb]
end CSeparatedNPComplete.SquarePartition
