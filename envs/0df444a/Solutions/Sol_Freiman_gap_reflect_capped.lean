-- Prove2me | solution 1 for Freiman.gap_reflect_capped
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:43:53.955405+00:00
-- url     : https://prove2.me/submissions/ca3ed4c0-0046-4b84-b284-f4ca87a54598

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_reflection

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) : gapCapped (gapReflect a) := by
  intro i
  rw [gap_reflection]
  exact hc (-i)
