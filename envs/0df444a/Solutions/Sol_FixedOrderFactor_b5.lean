-- Prove2me | solution 1 for FixedOrderFactor.b5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:53.500674+00:00
-- url     : https://prove2.me/submissions/4c3b37b4-519e-43f1-8aea-1af7b56ffe42

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, Nat.choose]
  norm_num
end FixedOrderFactor
