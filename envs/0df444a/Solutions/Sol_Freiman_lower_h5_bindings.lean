-- Prove2me | solution 1 for Freiman.lower_h5_bindings
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:42.615969+00:00
-- url     : https://prove2.me/submissions/465fe940-c71a-44bc-b21c-620d439a2f79

import Theorems.Thm_Freiman_lower_h5_catalog
import Theorems.Thm_Freiman_lower_h5_bindings_a
import Theorems.Thm_Freiman_lower_h5_bindings_b1
import Theorems.Thm_Freiman_lower_h5_bindings_b2h3
import Theorems.Thm_Freiman_lower_h5_bindings_b2h9h16
import Theorems.Thm_Freiman_lower_h5_bindings_b2h9not
import Theorems.Thm_Freiman_lower_h5_bindings_cLarge
import Theorems.Thm_Freiman_lower_h5_bindings_cShort
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution : lowerH5AllBindings := by
  intro c hc
  cases h : c.kind
  · exact lower_h5_bindings_a lower_h5_catalog c hc h
  · exact lower_h5_bindings_b1 lower_h5_catalog c hc h
  · exact lower_h5_bindings_b2h3 lower_h5_catalog c hc h
  · exact lower_h5_bindings_b2h9h16 lower_h5_catalog c hc h
  · exact lower_h5_bindings_b2h9not lower_h5_catalog c hc h
  · exact lower_h5_bindings_cLarge lower_h5_catalog c hc h
  · exact lower_h5_bindings_cShort lower_h5_catalog c hc h
