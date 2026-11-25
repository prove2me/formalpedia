-- Prove2me | solution 1 for DinitzGargGoemans.splitFlowMeetsDemands
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:54:26.380701+00:00
-- url     : https://prove2.me/submissions/6899d65f-a457-4dc8-bea8-e552ab6a53f1

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution :
    ∀ k, (∑ r, splitFlow k r) = demandAmount k := by
  intro k
  cases k <;> simp [splitFlow, demandAmount, Finset.sum_insert]
  all_goals norm_num
end DinitzGargGoemans
