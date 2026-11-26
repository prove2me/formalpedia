-- Prove2me | solution 1 for CSeparatedNPComplete.partition_gadget_schedule_partition_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:59:20.57961+00:00
-- url     : https://prove2.me/submissions/700b5e43-ad8a-46be-92b7-e691ffc07d69

module
public import Definitions.Def_CSeparatedNPComplete
public import Definitions.Def_CSeparatedNPComplete_Solution
public import Theorems.Thm_CSeparatedNPComplete_partition_gadget_schedule_pointwise_iff


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution
    (d : Nat) (a s : Vec d)
    (hd : 4 ≤ d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d s) ↔ is_ec_partition a s :=
  partition_gadget_schedule_pointwise_iff d a s hd hc hs
end CSeparatedNPComplete
