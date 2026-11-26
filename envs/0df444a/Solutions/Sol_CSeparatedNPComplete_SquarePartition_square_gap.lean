-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.square_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:25.876265+00:00
-- url     : https://prove2.me/submissions/ecc24aa6-3f06-41c5-953a-7cc5f451b401

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (u v : ℕ) (h : v ≤ u) :
    (u + v) ^ 2 = (u - v) ^ 2 + 4 * u * v := by
  have hsub := Nat.sub_add_cancel h
  nlinarith
end CSeparatedNPComplete.SquarePartition
