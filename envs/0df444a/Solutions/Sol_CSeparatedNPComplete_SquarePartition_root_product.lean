-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.root_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:47:17.493606+00:00
-- url     : https://prove2.me/submissions/41ff7b76-fd67-4076-a640-70eda3624640

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N K i ai : ℕ) (hi : i ≤ N) :
    K ^ (N + i) * (ai * K ^ (N - i)) = ai * K ^ (2 * N) := by
  calc
    K ^ (N + i) * (ai * K ^ (N - i)) = ai * (K ^ (N + i) * K ^ (N - i)) := by ring
    _ = ai * K ^ (2 * N) := by rw [← pow_add]; congr 2; omega
end CSeparatedNPComplete.SquarePartition
