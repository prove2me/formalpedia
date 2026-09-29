-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_early3_goal_ids
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:38:54.587555+00:00
-- url     : https://prove2.me/submissions/093f78a8-4fcb-41ac-a4cd-39007ae84cd2

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
private instance decEarlyGoalValid (C : LowerEarlyTerminalCatalog) (g : LowerEarlyTerminalGoal) : Decidable (lowerEarlyTerminalGoalValid C g) := by
  rcases g with ⟨premises,kind⟩
  cases kind <;> unfold lowerEarlyTerminalGoalValid <;> infer_instance
theorem solution : ∀ g ∈ lowerEarlyTerminalEarly3.goals, lowerEarlyTerminalGoalValid lowerEarlyTerminalEarly3 g := by
  decide +kernel
#print axioms solution
