-- Prove2me | solution 1 for Freiman.late_all_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:14.86798+00:00
-- url     : https://prove2.me/submissions/bd1fbe00-00fa-4a6c-ac9a-0919b2c146cd

import Theorems.Thm_Freiman_late_catalog_sizes
import Theorems.Thm_Freiman_late_witnesses_0000_0185
import Theorems.Thm_Freiman_late_witnesses_0185_0370
import Theorems.Thm_Freiman_late_witnesses_0370_0555
import Theorems.Thm_Freiman_late_witnesses_0555_0740
import Theorems.Thm_Freiman_late_witnesses_0740_0925
import Theorems.Thm_Freiman_late_witnesses_0925_1110
import Theorems.Thm_Freiman_late_witnesses_1110_1295
import Theorems.Thm_Freiman_late_witnesses_1295_1473
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : lateAllWitnesses lateCatalog := by
  intro id hid
  rcases hid with ⟨hpos,hle⟩
  rw [late_catalog_sizes.2.1] at hle
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : id ≠ 0)
  by_cases h0 : i < 185
  · exact late_witnesses_0000_0185 i (by omega) h0
  by_cases h1 : i < 370
  · exact late_witnesses_0185_0370 i (by omega) h1
  by_cases h2 : i < 555
  · exact late_witnesses_0370_0555 i (by omega) h2
  by_cases h3 : i < 740
  · exact late_witnesses_0555_0740 i (by omega) h3
  by_cases h4 : i < 925
  · exact late_witnesses_0740_0925 i (by omega) h4
  by_cases h5 : i < 1110
  · exact late_witnesses_0925_1110 i (by omega) h5
  by_cases h6 : i < 1295
  · exact late_witnesses_1110_1295 i (by omega) h6
  exact late_witnesses_1295_1473 i (by omega) (by omega)
