-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:11.41704+00:00
-- url     : https://prove2.me/submissions/da0a2136-9a53-4044-bc0a-c7f1abce84f8

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_square_gap
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_upper_bound_root
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_root_product

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (a : ℕ → ℕ) (K i : ℕ) (hi : i < N)
    (ha : a i ≤ K ^ (2 * i)) :
    plus N a K i = minus N a K i + 4 * K ^ (2 * N) * a i := by
  unfold plus minus
  rw [square_gap _ _ (upper_bound_root N K i (a i) (by omega) ha)]
  have h := root_product N K i (a i) (by omega)
  nlinarith
end CSeparatedNPComplete.SquarePartition
