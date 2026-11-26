-- Prove2me | solution 1 for FixedOrderFactor.b7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:10.070437+00:00
-- url     : https://prove2.me/submissions/ab0fa7ba-2ab5-4bab-9425-cebed169d857

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_b5
public import Theorems.Thm_FixedOrderFactor_b6

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : bernoulli' 7 = 0 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, b5, b6, Nat.choose]
  norm_num
end FixedOrderFactor
