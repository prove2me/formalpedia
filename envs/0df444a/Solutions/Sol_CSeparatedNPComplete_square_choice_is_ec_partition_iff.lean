-- Prove2me | solution 1 for CSeparatedNPComplete.square_choice_is_ec_partition_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:44.728416+00:00
-- url     : https://prove2.me/submissions/97464aff-48c4-447f-853b-75c2dc253cdb

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_for_choice_iff
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_selector_is_ec_partition_iff


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    is_ec_partition (SquarePartition.selector N b) (SquarePartition.values N a K) ↔
      SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) :=
  (SquarePartition.selector_is_ec_partition_iff N a K b).trans
    (SquarePartition.for_choice_iff N a K b hK hbound)
end CSeparatedNPComplete
