-- Prove2me | solution 1 for Freiman.lower_early_second_chain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:26.215637+00:00
-- url     : https://prove2.me/submissions/2da3c1c4-9c1a-4f5b-baa4-c34ab1df8700

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push


import Theorems.Thm_Freiman_lowerEarlyTerminal_short_ready

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) (h27 : ¬ lowerA p 27) (h34 : lowerA p 34) : lowerEarlyGeometry p := by
  have h := lowerEarlyTerminal_short_ready t p hs hd 1 (by omega) ⟨h27,h34⟩
  simpa [lowerEarlyGeometry,lowerEarlyTerminalListGeometry,lowerEarlyList,h27,h34,lowerEarlyTerminalSecond] using h
