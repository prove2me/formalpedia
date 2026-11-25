-- Prove2me | solution 1 for DinitzGargGoemans.weakDggCostConjectureFalse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:22.432987+00:00
-- url     : https://prove2.me/submissions/03073de3-461d-4a72-9efa-0f4d4a8fdcdc

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_counterexampleWellFormed
import Theorems.Thm_DinitzGargGoemans_splitFlowFeasible
import Theorems.Thm_DinitzGargGoemans_noWeakDggRounding

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution :
    ¬ (∀ (I : PathFlowInstance Commodity RouteChoice Arc)
        (f : Commodity → RouteChoice → ℚ),
        wellFormedInstance I ∧ fractionalFeasible I f →
          weakDggProperty I f) := by
  intro h
  exact noWeakDggRounding
    (h counterexampleInstance splitFlow
      ⟨counterexampleWellFormed, splitFlowFeasible⟩)
end DinitzGargGoemans
