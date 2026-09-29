-- Prove2me | solution 1 for Freiman.lower_terminal_state1
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:26.173281+00:00
-- url     : https://prove2.me/submissions/d374eff4-8699-4ad2-8a51-cd60af4c3afe

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push


import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_ready

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34)
    (he : lowerEnds (lowerNormalize p).1 [1]) : lowerEarlyGeometry p := by
  classical
  have h := lowerEarlyTerminal_terminal_ready t p hs hd h27 h34 0 he
  by_cases h40 : lowerA p 40 <;>
    simpa [lowerEarlyGeometry,lowerEarlyTerminalListGeometry,lowerEarlyList,h27,h34,h40,
    lowerEarlyTerminalTerminal,lowerEarlyTerminalCommon,lowerEarlyTerminalLast,
    lowerEarlyTerminalMiddle, lowerEarlyTerminalPrimary] using h
