-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state1_goal_ids
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:38:55.423971+00:00
-- url     : https://prove2.me/submissions/861162b0-d669-4846-a4e8-bd5ae1c6a85c

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
private instance decEarlyGoalValid (C : LowerEarlyTerminalCatalog) (g : LowerEarlyTerminalGoal) : Decidable (lowerEarlyTerminalGoalValid C g) := by
  rcases g with ⟨premises,kind⟩
  cases kind <;> unfold lowerEarlyTerminalGoalValid <;> infer_instance
theorem solution : ∀ g ∈ lowerEarlyTerminalState1.goals, lowerEarlyTerminalGoalValid lowerEarlyTerminalState1 g := by
  decide +kernel
#print axioms solution
