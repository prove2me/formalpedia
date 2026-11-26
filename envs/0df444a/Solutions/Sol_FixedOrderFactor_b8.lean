-- Prove2me | solution 1 for FixedOrderFactor.b8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:29.14431+00:00
-- url     : https://prove2.me/submissions/fb6a799a-b484-43eb-90f6-0c7a02bbe439

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_b5
public import Theorems.Thm_FixedOrderFactor_b6
public import Theorems.Thm_FixedOrderFactor_b7

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, b5, b6, b7, Nat.choose]
  norm_num
end FixedOrderFactor
