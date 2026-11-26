-- Prove2me | solution 1 for CSeparatedNPComplete.square_partition_implies_partition_for_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:40.368215+00:00
-- url     : https://prove2.me/submissions/eb7d8d6a-cdd3-4f08-ae1d-c635a0535ad5

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
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i))
    (h : SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) :
    SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) :=
  (SquarePartition.for_choice_iff N a K b hK hbound).mp h
end CSeparatedNPComplete
