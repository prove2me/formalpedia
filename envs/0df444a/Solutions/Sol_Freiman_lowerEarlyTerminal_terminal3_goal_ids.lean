-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal3_goal_ids
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:38:56.945835+00:00
-- url     : https://prove2.me/submissions/171a8498-6caa-4f3d-bc1b-2c1cdb3a193b

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
private instance decEarlyGoalValid (C : LowerEarlyTerminalCatalog) (g : LowerEarlyTerminalGoal) : Decidable (lowerEarlyTerminalGoalValid C g) := by
  rcases g with ⟨premises,kind⟩
  cases kind <;> unfold lowerEarlyTerminalGoalValid <;> infer_instance
theorem solution : ∀ g ∈ lowerEarlyTerminalTerminal3.goals, lowerEarlyTerminalGoalValid lowerEarlyTerminalTerminal3 g := by
  decide +kernel
#print axioms solution
