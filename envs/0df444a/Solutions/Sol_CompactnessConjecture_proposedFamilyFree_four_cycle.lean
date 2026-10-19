-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_four_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/374470b0-f13c-4c98-b44b-f4865b158f27

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_four_cycle_mem_proposedFamily

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 4).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member four_cycle_mem_proposedFamily hfree
end CompactnessConjecture
