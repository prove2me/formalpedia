-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_six_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/913d5541-5238-464b-b6ac-541875f2a1fb

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_six_cycle_mem_proposedFamily

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 6).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member six_cycle_mem_proposedFamily hfree
end CompactnessConjecture
