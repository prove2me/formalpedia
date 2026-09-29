-- Prove2me | solution 1 for Freiman.lower_h5_numerics
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:57.415075+00:00
-- url     : https://prove2.me/submissions/1df54924-31a6-4f94-9117-20d3250c488d

import Theorems.Thm_Freiman_lower_h5_finite_transfer
import Theorems.Thm_Freiman_lower_h5_record_exclusion
import Theorems.Thm_Freiman_lower_h5_bindings
import Theorems.Thm_Freiman_lower_h5_witnesses
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution : ∀ c ∈ lowerH5Cases, lowerH5Numeric c := by
  exact lower_h5_finite_transfer lower_h5_record_exclusion lower_h5_bindings lower_h5_witnesses
