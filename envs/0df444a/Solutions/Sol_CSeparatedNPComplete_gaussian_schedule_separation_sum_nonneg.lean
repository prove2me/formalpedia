-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_schedule_separation_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:46:48.360463+00:00
-- url     : https://prove2.me/submissions/e357e3fd-d578-4d41-9050-8dcdbb488ba2

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (m : ℝ) (i k : Nat) :
    0 ≤ gaussian_schedule_separation_sum m i k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
end CSeparatedNPComplete
