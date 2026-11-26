-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.selector_is_ec_partition_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:55.673192+00:00
-- url     : https://prove2.me/submissions/e3b31211-079a-4f1d-97e3-c411a88579a9

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_selector_binary
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_selector_card
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_selected_sum
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_total_sum

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    is_ec_partition (selector N b) (values N a K) ↔
      leftSum N N a K b = rightSum N N a K b := by
  have hbin := selector_binary N b
  have hcard := selector_card N b
  rw [is_ec_partition, selected_sum, total_sum N a K b]
  constructor
  · rintro ⟨_, _, h⟩
    exact_mod_cast (show (leftSum N N a K b : ℝ) = (rightSum N N a K b : ℝ) by linarith)
  · intro h
    refine ⟨hbin, ?_, ?_⟩
    · rw [hcard]
      push_cast
      ring
    · rw [h]
      ring
end CSeparatedNPComplete.SquarePartition
