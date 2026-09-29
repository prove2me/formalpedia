-- Prove2me | solution 1 for Freiman.late_all_paths
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:15.073161+00:00
-- url     : https://prove2.me/submissions/12b20772-32d1-438e-9c24-e32df01b1f72

import Theorems.Thm_Freiman_late_catalog_sizes
import Theorems.Thm_Freiman_late_paths_00_16
import Theorems.Thm_Freiman_late_paths_16_32
import Theorems.Thm_Freiman_late_paths_32_48
import Theorems.Thm_Freiman_late_paths_48_63
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : lateAllPaths lateCatalog := by
  intro id hid
  rcases hid with ⟨hpos,hle⟩
  rw [late_catalog_sizes.2.2.2.1] at hle
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : id ≠ 0)
  by_cases h0 : i < 16
  · exact late_paths_00_16 i (by omega) h0
  by_cases h1 : i < 32
  · exact late_paths_16_32 i (by omega) h1
  by_cases h2 : i < 48
  · exact late_paths_32_48 i (by omega) h2
  exact late_paths_48_63 i (by omega) (by omega)
