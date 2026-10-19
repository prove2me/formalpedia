-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_member_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/696a04c6-1512-427b-85ef-cbbe8dfb8657

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_induction
import Theorems.Thm_CompactnessConjecture_encodedJQuotient_isBipartite
import Theorems.Thm_CompactnessConjecture_encodedKQuotient_isBipartite

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.IsBipartite :=
  proposedFamily_induction (P := fun graph => graph.graph.IsBipartite)
    (SimpleGraph.cycleGraph.bicoloring_of_even 4 (by decide)).colorable
    (SimpleGraph.cycleGraph.bicoloring_of_even 6 (by decide)).colorable
    (fun _ hf => encodedJQuotient_isBipartite hf)
    (fun _ hf => encodedKQuotient_isBipartite hf)
    forbidden hforbidden
end CompactnessConjecture
