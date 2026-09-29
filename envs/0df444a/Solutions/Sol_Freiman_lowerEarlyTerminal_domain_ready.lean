-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_domain_ready
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:39.185488+00:00
-- url     : https://prove2.me/submissions/522e5139-67fb-4116-85e2-9235250b8d85

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_domain_classes
import Theorems.Thm_Freiman_lowerEarlyTerminal_domain_context
import Theorems.Thm_Freiman_lowerEarlyTerminal_domain_rectangle
import Theorems.Thm_Freiman_lowerEarlyTerminal_domain_laws

open Freiman

theorem solution : LowerEarlyTerminalDomainLaws := by
  exact lowerEarlyTerminal_domain_laws lowerEarlyTerminal_domain_classes
    lowerEarlyTerminal_domain_context lowerEarlyTerminal_domain_rectangle
