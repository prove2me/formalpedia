-- Prove2me | solution 1 for FixedOrderFactor.b6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:10.341606+00:00
-- url     : https://prove2.me/submissions/f4162951-f686-4567-b72d-bacefe426fd6

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_b5

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, b5, Nat.choose]
  norm_num
end FixedOrderFactor
