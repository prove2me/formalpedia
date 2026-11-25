-- Prove2me | solution 1 for DinitzGargGoemans.strictDggCostConjectureFalse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:19:01.938175+00:00
-- url     : https://prove2.me/submissions/6ed912a2-acb7-4236-ab2e-9fbdf0049ed2

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_counterexampleWellFormed
import Theorems.Thm_DinitzGargGoemans_splitFlowFeasible
import Theorems.Thm_DinitzGargGoemans_noStrictDggRounding

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution :
    ¬ (∀ (I : PathFlowInstance Commodity RouteChoice Arc)
        (f : Commodity → RouteChoice → ℚ),
        wellFormedInstance I ∧ fractionalFeasible I f →
          strictDggProperty I f) := by
  intro h
  exact noStrictDggRounding
    (h counterexampleInstance splitFlow
      ⟨counterexampleWellFormed, splitFlowFeasible⟩)
end DinitzGargGoemans
