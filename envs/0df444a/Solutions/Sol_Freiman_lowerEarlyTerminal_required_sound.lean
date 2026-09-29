-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_required_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:08.039409+00:00
-- url     : https://prove2.me/submissions/cc1e0fd9-506d-4267-a3ea-fed4b1aaad3f

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_law
import Theorems.Thm_Freiman_lowerEarlyTerminal_greater_law
import Theorems.Thm_Freiman_lowerEarlyTerminal_catalog_sound
import Theorems.Thm_Freiman_lowerEarlyTerminal_compare_transfer
import Theorems.Thm_Freiman_lowerEarlyTerminal_union_transfer
import Theorems.Thm_Freiman_lowerEarlyTerminal_requirements_transfer

open Freiman

theorem solution (C : LowerEarlyTerminalCatalog) (p : LowerPair) (mode : ℕ)
    (hm : lowerEarlyTerminalMatches p C)
    (hr : certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p))
    (hv : lowerEarlyTerminalFiniteValid C) (hb : lowerEarlyTerminalRequirementBinding C mode) :
    lowerEarlyTerminalRequiredSound C p mode := by
  exact lowerEarlyTerminal_requirements_transfer lowerEarlyTerminal_endpoint_law lowerEarlyTerminal_greater_law
    C p mode hm hr hb (lowerEarlyTerminal_catalog_sound C hv)
    (fun u hi v hj strict h => lowerEarlyTerminal_compare_transfer lowerEarlyTerminal_endpoint_law
      lowerEarlyTerminal_greater_law C p hm u v hi hj strict h)
    (fun h => lowerEarlyTerminal_union_transfer lowerEarlyTerminal_endpoint_law
      lowerEarlyTerminal_greater_law C p hm h)
