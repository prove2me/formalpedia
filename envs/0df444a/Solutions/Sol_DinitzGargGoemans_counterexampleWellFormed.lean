-- Prove2me | solution 1 for DinitzGargGoemans.counterexampleWellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:50:41.017255+00:00
-- url     : https://prove2.me/submissions/ea808710-aae3-4b3c-b431-623c20ebd6cc

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
    wellFormedInstance counterexampleInstance := by
  constructor
  · intro k
    cases k <;> simp [counterexampleInstance, demandAmount]
  · intro a
    cases a <;> norm_num [counterexampleInstance, arcCapacity, arcCost]
end DinitzGargGoemans
