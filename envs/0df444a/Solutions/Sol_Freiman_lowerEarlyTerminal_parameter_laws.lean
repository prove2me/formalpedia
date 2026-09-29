-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_parameter_laws
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:10.223721+00:00
-- url     : https://prove2.me/submissions/36844489-3541-472e-b4d7-fcfec72b3e1a

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_h7
import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_h18
import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_a9
import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_h27
import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_h34
import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_d40
import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_d46

open Freiman

theorem solution : LowerEarlyTerminalParameterLaws := by
  intro p
  exact ⟨lowerEarlyTerminal_parameter_h7 p, lowerEarlyTerminal_parameter_h18 p, lowerEarlyTerminal_parameter_a9 p, lowerEarlyTerminal_parameter_h27 p, lowerEarlyTerminal_parameter_h34 p, lowerEarlyTerminal_parameter_d40 p, lowerEarlyTerminal_parameter_d46 p⟩
