-- Prove2me | solution 1 for Freiman.lower_equal_three_good
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:04.015839+00:00
-- url     : https://prove2.me/submissions/924be639-910f-475d-b31b-4dbb872d9fd5

import Theorems.Thm_Freiman_lower_equal_three_source_good
import Theorems.Thm_Freiman_lower_source_cover_identity
import Definitions.Def_Freiman_lowerSourceCover
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p)
    (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p)
    (hwide : lowerWidth p.2 ≤ lowerWidth p.1)
    (hratio : lowerWidth p.1 < (19/5 : ℝ)*lowerWidth p.2) : lowerGood p := by
  have hg := lower_equal_three_source_good p ha hp hl hr hb hwide hratio
  simpa only [lowerSourceGood, lowerGood, lower_source_cover_identity] using hg
