-- Prove2me | solution 1 for CohnElkies.uniformAdmissibleLowerBound_of_signRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/3704b48a-e336-4283-9376-419271eef356

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedCost_nonneg
import Theorems.Thm_CohnElkies_normalizedCost_ge_of_no_antiFourierWitness

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hsign : UniformAntiFourierSignRadius) :
    UniformAdmissibleLowerBound := by
  intro c hc
  by_cases hpositive : 0 < c
  · filter_upwards [hsign c hpositive hc,
      eventually_gt_atTop (0 : ℕ)] with d hno hd
    intro f
    exact normalizedCost_ge_of_no_antiFourierWitness f hd c hno
  · exact Filter.Eventually.of_forall fun d f =>
      (le_of_not_gt hpositive).trans (normalizedCost_nonneg f)
end CohnElkies
