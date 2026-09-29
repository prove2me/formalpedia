-- Prove2me | solution 1 for Freiman.lower_early_first_chain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:26.032034+00:00
-- url     : https://prove2.me/submissions/25dfc9d1-8d7f-4527-870f-48990f84f401

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push


import Theorems.Thm_Freiman_lowerEarlyTerminal_short_ready

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) (h27 : lowerA p 27) : lowerEarlyGeometry p := by
  have h := lowerEarlyTerminal_short_ready t p hs hd 0 (by omega) h27
  simpa [lowerEarlyGeometry,lowerEarlyTerminalListGeometry,lowerEarlyList,h27,lowerEarlyTerminalFirst] using h
