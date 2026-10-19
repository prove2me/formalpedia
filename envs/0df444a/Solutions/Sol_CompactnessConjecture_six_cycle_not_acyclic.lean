-- Prove2me | solution 1 for CompactnessConjecture.six_cycle_not_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/d0bbc46d-f7a9-4058-af1b-b44e1a174ec4

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution :
    ¬ (finiteCycle 6).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 3)
    SimpleGraph.cycleGraph.isCycle_cycle
end CompactnessConjecture
