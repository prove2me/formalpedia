-- Prove2me | solution 1 for Freiman.gap_maximum_reflected
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:43:54.04363+00:00
-- url     : https://prove2.me/submissions/eaa46924-c1af-4267-87fe-893d2d6d7813

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_maximum_bound
import Theorems.Thm_Freiman_gap_reflect_capped
import Theorems.Thm_Freiman_gap_reflect_match
import Theorems.Thm_Freiman_gap_reflection

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedA ∨ gapMatch a 0 (gapReverse gapSeedA)) : localValue a 0 ≤ gapLeft := by
  rcases hs with hs | hs
  · exact gap_maximum_bound a hc hs
  · have h := gap_maximum_bound (gapReflect a) (gap_reflect_capped a hc) (gap_reflect_match a gapSeedA (by decide) hs)
    simpa only [gap_reflection, neg_zero] using h
