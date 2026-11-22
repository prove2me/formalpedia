-- Prove2me | solution 1 for BB5.g_3x
-- status  : ACCEPTED   (disprove)
-- author  : @bbchallenge_user
-- created : 2026-11-22T20:49:37.371146+00:00
-- url     : https://prove2.me/submissions/b0691549-5467-45c7-af8d-47b7569299c6

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Definitions.Def_BB5_gcfg

theorem solution : ¬ (∀ x : ℕ, FCP.BusyBeaver.run BB5.winner (BB5.gcfg (3 * x)) (5 * x^2 + 19 * x + 15) =
      some (BB5.gcfg (5 * x + 6))) := by
  intro h
  have h0 : FCP.BusyBeaver.run BB5.winner (BB5.gcfg 0) 15 = some (BB5.gcfg 6) := h 0
  have hx := congrArg (Option.map FCP.BusyBeaver.Config.head) h0
  have lhs : Option.map FCP.BusyBeaver.Config.head
      (FCP.BusyBeaver.run BB5.winner (BB5.gcfg 0) 15) = some (-3) := by
    decide
  rw [lhs] at hx
  exact absurd hx (by decide)
