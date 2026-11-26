-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.for_choice_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:49.999941+00:00
-- url     : https://prove2.me/submissions/2709b61a-d5cd-4ffd-bc1e-917153fe957e

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_right_as_left
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_left_decomp

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    leftSum N N a K b = rightSum N N a K b ↔
      chooseSum N a b = chooseSum N a (fun i => !(b i)) := by
  rw [right_as_left, left_decomp N N a K b le_rfl hbound,
    left_decomp N N a K (fun i => !(b i)) le_rfl hbound]
  have hfactor : 0 < 4 * K ^ (2 * N) := by positivity
  constructor <;> intro h <;> nlinarith
end CSeparatedNPComplete.SquarePartition
