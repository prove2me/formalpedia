-- Prove2me | solution 1 for Freiman.gap_minimum_reflected
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:44:07.824632+00:00
-- url     : https://prove2.me/submissions/9a78907a-c691-4126-8cc6-0eaa9b3529c7

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_minimum_bound
import Theorems.Thm_Freiman_gap_reflect_capped
import Theorems.Thm_Freiman_gap_reflect_match
import Theorems.Thm_Freiman_gap_reflection

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedB ∨ gapMatch a 0 (gapReverse gapSeedB)) : localValue a 0 ≥ cF := by
  rcases hs with hs | hs
  · exact gap_minimum_bound a hc hs
  · have h := gap_minimum_bound (gapReflect a) (gap_reflect_capped a hc) (gap_reflect_match a gapSeedB (by decide) hs)
    simpa only [gap_reflection, neg_zero] using h
