-- Prove2me | solution 1 for Freiman.lower_h5_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:42.258663+00:00
-- url     : https://prove2.me/submissions/11c46538-be4b-485a-bac6-52b9c204a5ad

import Theorems.Thm_Freiman_lower_h5_catalog
import Theorems.Thm_Freiman_lower_h5_witness_batch1
import Theorems.Thm_Freiman_lower_h5_witness_batch2
import Theorems.Thm_Freiman_lower_h5_witness_batch3
import Theorems.Thm_Freiman_lower_h5_witness_batch4
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution : lowerH5AllWitnesses := by
  intro i hi hmax
  have hn : i ≤ 71 := by simpa only [lower_h5_catalog.2.2.2.1] using hmax
  by_cases h1 : i ≤ 18
  · exact lower_h5_witness_batch1 i hi h1
  by_cases h2 : i ≤ 36
  · exact lower_h5_witness_batch2 i (by omega) h2
  by_cases h3 : i ≤ 54
  · exact lower_h5_witness_batch3 i (by omega) h3
  · exact lower_h5_witness_batch4 i (by omega) hn
