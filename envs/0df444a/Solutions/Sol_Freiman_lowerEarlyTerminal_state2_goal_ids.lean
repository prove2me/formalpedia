-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state2_goal_ids
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:38:56.198398+00:00
-- url     : https://prove2.me/submissions/f189de64-eb0a-4e43-9051-4cb58cb595c1

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
private instance decEarlyGoalValid (C : LowerEarlyTerminalCatalog) (g : LowerEarlyTerminalGoal) : Decidable (lowerEarlyTerminalGoalValid C g) := by
  rcases g with ⟨premises,kind⟩
  cases kind <;> unfold lowerEarlyTerminalGoalValid <;> infer_instance
theorem solution : ∀ g ∈ lowerEarlyTerminalState2.goals, lowerEarlyTerminalGoalValid lowerEarlyTerminalState2 g := by
  decide +kernel
#print axioms solution
