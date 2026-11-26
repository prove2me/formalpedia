-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_gamma_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:57.706477+00:00
-- url     : https://prove2.me/submissions/896f24f9-eb02-4416-ae74-17da5c76582f

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
theorem _root_.solution (n : Nat) {m : ℝ} (hm : 1 ≤ m) :
    1 ≤ second_gadget_gamma n m :=
  hm.trans (le_add_of_nonneg_right (gaussian_schedule_separation_sum_nonneg m n n))
end CSeparatedNPComplete
