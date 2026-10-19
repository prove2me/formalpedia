-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_member_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/6f2e9b62-e4f6-4cf6-919c-c35718e99309

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_induction
import Theorems.Thm_CompactnessConjecture_encodedJQuotient_connected
import Theorems.Thm_CompactnessConjecture_encodedKQuotient_connected
import Theorems.Thm_CompactnessConjecture_finiteCycle_connected

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.Connected :=
  proposedFamily_induction (P := fun graph => graph.graph.Connected)
    (finiteCycle_connected (by norm_num : 0 < (4 : ℕ)))
    (finiteCycle_connected (by norm_num : 0 < (6 : ℕ)))
    (fun _ hf => encodedJQuotient_connected hf)
    (fun _ hf => encodedKQuotient_connected hf)
    forbidden hforbidden
end CompactnessConjecture
