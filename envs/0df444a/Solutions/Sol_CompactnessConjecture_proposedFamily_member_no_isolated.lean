-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_member_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/3e8db812-cb30-40f6-87c6-30507de30761

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_induction
import Theorems.Thm_CompactnessConjecture_cycleGraph_no_isolated
import Theorems.Thm_CompactnessConjecture_encodedJQuotient_no_isolated
import Theorems.Thm_CompactnessConjecture_encodedKQuotient_no_isolated

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    GraphHasNoIsolated forbidden.graph :=
  proposedFamily_induction (P := fun graph => GraphHasNoIsolated graph.graph)
    (cycleGraph_no_isolated 2) (cycleGraph_no_isolated 4)
    (fun _ hf => encodedJQuotient_no_isolated hf)
    (fun _ hf => encodedKQuotient_no_isolated hf)
    forbidden hforbidden
end CompactnessConjecture
