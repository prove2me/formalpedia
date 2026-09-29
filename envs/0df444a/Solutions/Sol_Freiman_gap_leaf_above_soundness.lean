-- Prove2me | solution 1 for Freiman.gap_leaf_above_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:44:08.311675+00:00
-- url     : https://prove2.me/submissions/969cc2b7-e235-4660-b335-fd51f5b1738c

import Definitions.Def_Freiman_gapCertificate
import Theorems.Thm_Freiman_gap_cylinder_semantics

open Freiman

theorem solution (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (j : ℕ) (hcheck : gapLeafCheck lower upper mode s (.above j)) : gapModeOutcome mode a i := by
  have hb := (gap_cylinder_semantics a i s j hd hm hcheck.1).1
  have hq : gapCap ≤ (gapCylinderLower s.word j : ℝ) := by
    dsimp only [gapCap]
    have hcast : ((4527829567/1000000000 : ℚ) : ℝ) ≤ (gapCylinderLower s.word j : ℝ) := (Rat.cast_le (K := ℝ)).mpr hcheck.2
    norm_num at hcast
    exact hcast
  exact False.elim ((not_lt_of_ge (hc (i+(j : ℤ)-(s.centre : ℤ)))) (lt_of_le_of_lt hq hb))
