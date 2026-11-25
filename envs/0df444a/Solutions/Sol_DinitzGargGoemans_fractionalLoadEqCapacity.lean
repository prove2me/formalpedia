-- Prove2me | solution 1 for DinitzGargGoemans.fractionalLoadEqCapacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:50:46.396937+00:00
-- url     : https://prove2.me/submissions/1851e1ad-15e3-47a0-af91-2ad08083be8f

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
    ∀ a, fractionalLoad counterexampleInstance splitFlow a = arcCapacity a := by
  intro a
  cases a <;>
    simp [fractionalLoad, counterexampleInstance, counterexampleUses,
      routeEdges, splitFlow, arcCapacity, Finset.sum_insert]
  all_goals norm_num
end DinitzGargGoemans
