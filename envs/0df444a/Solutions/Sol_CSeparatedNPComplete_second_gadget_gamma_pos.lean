-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_gamma_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:56.947666+00:00
-- url     : https://prove2.me/submissions/0a02a742-b4ef-438a-9643-1ed855c23eee

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_nonneg

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (n : Nat) {m : ℝ} (hm : 0 < m) :
    0 < second_gadget_gamma n m :=
  add_pos_of_pos_of_nonneg hm (gaussian_schedule_separation_sum_nonneg m n n)
end CSeparatedNPComplete
