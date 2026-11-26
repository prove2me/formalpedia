-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseStepFactor_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:31.653804+00:00
-- url     : https://prove2.me/submissions/54868865-c2ec-4b13-a2b7-2b2257972d7e

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_one
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_nonneg
import Theorems.Thm_FirstPassageLinearTransport_reverseStepFactor_eq_one_sub_reverseLoss


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n i : ℕ} (hn : 0 < n) :
    0 ≤ reverseStepFactor n i ∧ reverseStepFactor n i ≤ 1 := by
  rw [reverseStepFactor_eq_one_sub_reverseLoss]
  constructor
  · linarith [reverseLoss_le_one hn i]
  · linarith [reverseLoss_nonneg n i]
end FirstPassageLinearTransport
