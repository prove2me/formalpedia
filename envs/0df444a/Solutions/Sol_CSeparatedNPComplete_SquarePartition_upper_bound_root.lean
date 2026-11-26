-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.upper_bound_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:32.031957+00:00
-- url     : https://prove2.me/submissions/9b5f9827-d85d-430b-a33c-4544e0088d22

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N K i ai : ℕ) (hi : i ≤ N)
    (ha : ai ≤ K ^ (2 * i)) : ai * K ^ (N - i) ≤ K ^ (N + i) := by
  calc
    ai * K ^ (N - i) ≤ K ^ (2 * i) * K ^ (N - i) := Nat.mul_le_mul_right _ ha
    _ = K ^ (N + i) := by rw [← pow_add]; congr 1; omega
end CSeparatedNPComplete.SquarePartition
