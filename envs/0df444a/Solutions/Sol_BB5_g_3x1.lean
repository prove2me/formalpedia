-- Prove2me | solution 1 for BB5.g_3x1
-- status  : ACCEPTED   (disprove)
-- author  : @bbchallenge_user
-- created : 2026-11-22T20:49:39.064118+00:00
-- url     : https://prove2.me/submissions/c03d3391-4cf3-4abd-bba6-4ee0138e9a94

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Definitions.Def_BB5_gcfg

theorem solution : ¬ (∀ x : ℕ, FCP.BusyBeaver.run BB5.winner (BB5.gcfg (3 * x + 1)) (5 * x^2 + 25 * x + 27) =
      some (BB5.gcfg (5 * x + 9))) := by
  intro h
  have h0 : FCP.BusyBeaver.run BB5.winner (BB5.gcfg 1) 27 = some (BB5.gcfg 9) := h 0
  have hx := congrArg (Option.map FCP.BusyBeaver.Config.head) h0
  have lhs : Option.map FCP.BusyBeaver.Config.head
      (FCP.BusyBeaver.run BB5.winner (BB5.gcfg 1) 27) = some (-5) := by
    decide
  rw [lhs] at hx
  exact absurd hx (by decide)
