-- Prove2me | solution 1 for Freiman.other22_path_shapes
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:45:15.122644+00:00
-- url     : https://prove2.me/submissions/072980eb-d944-4470-b2e2-4961e178d50b

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

instance scoutDecLegalSteps (s : LowerHistoryState) : ∀ ls, Decidable (lowerHistoryLegalSteps s ls)
  | [] => inferInstanceAs (Decidable True)
  | (l,r)::ls => by
      unfold lowerHistoryLegalSteps
      have := scoutDecLegalSteps (lowerHistoryAdvance s l r) ls
      infer_instance

theorem solution : ∀ k : Fin 6, lowerHistoryStructural (other22Paths k) := by
  intro k
  fin_cases k <;> unfold lowerHistoryStructural <;> decide +kernel

#print axioms solution
