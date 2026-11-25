-- Prove2me | solution 1 for DinitzGargGoemans.splitFlowFeasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:57:58.79012+00:00
-- url     : https://prove2.me/submissions/e87d842a-e989-4ddd-83dc-10b3efab568a

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_counterexampleWellFormed
import Theorems.Thm_DinitzGargGoemans_splitFlowMeetsDemands
import Theorems.Thm_DinitzGargGoemans_fractionalLoadEqCapacity
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution :
    fractionalFeasible counterexampleInstance splitFlow := by
  refine ⟨counterexampleWellFormed, ?_, ?_, ?_, ?_⟩
  · intro k r
    cases k <;> cases r <;> norm_num [splitFlow]
  · intro k r h
    simp [counterexampleInstance] at h
  · intro k
    simpa [counterexampleInstance] using splitFlowMeetsDemands k
  · intro a
    rw [fractionalLoadEqCapacity]
    simp [counterexampleInstance]
end DinitzGargGoemans
