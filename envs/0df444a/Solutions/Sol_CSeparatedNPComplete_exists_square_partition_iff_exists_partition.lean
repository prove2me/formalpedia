-- Prove2me | solution 1 for CSeparatedNPComplete.exists_square_partition_iff_exists_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:37.545425+00:00
-- url     : https://prove2.me/submissions/63510d76-3bf7-4da5-9f37-99467433ee80

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_for_choice_iff


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    (∃ b, SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) ↔
      ∃ b, SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by
  exact exists_congr fun b => SquarePartition.for_choice_iff N a K b hK hbound
end CSeparatedNPComplete
