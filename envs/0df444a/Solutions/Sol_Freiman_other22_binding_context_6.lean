-- Prove2me | solution 1 for Freiman.other22_binding_context_6
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:45:14.170448+00:00
-- url     : https://prove2.me/submissions/aba314a8-cd35-4690-b859-8900191e53b2

-- Adapted exact finite-check structure from Mahakusaladhamma submission f7280414-8861-4d94-a6c7-2b2cde0279c1; establishes a distinct context.
import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

theorem solution : other22CaseBinding 5 := by
  refine ⟨?_, ?_⟩
  · unfold other22RecordBinding
    decide +kernel
  · have key : ∀ ai < (lowerHistorySourcePremises (other22Paths 5)).length,
        ∀ bi < (lowerHistoryEndpointComparisons (other22Paths 5)).length,
          ∃ r ∈ other22Records, r.caseId = 5 ∧ r.alternative = ai ∧ r.branch = bi := by
      decide +kernel
    intro ai hai bi cs g hbi
    exact (List.getElem_of_getElem? hbi).elim fun hlt _ => key ai hai bi hlt

#print axioms solution
