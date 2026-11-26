-- Prove2me | solution 1 for CSeparatedNPComplete.exists_square_partition_implies_exists_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:35.666379+00:00
-- url     : https://prove2.me/submissions/4ebbe5bb-39cc-4adb-ac07-c38f10585c30

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
public import Theorems.Thm_CSeparatedNPComplete_square_partition_implies_partition_for_choice

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i))
    (h : ∃ b, SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) :
    ∃ b, SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, square_partition_implies_partition_for_choice N a K b hK hbound hb⟩
end CSeparatedNPComplete
