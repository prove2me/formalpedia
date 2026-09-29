-- Prove2me | solution 1 for Freiman.lower_geometry_equal_large_left
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:47.059976+00:00
-- url     : https://prove2.me/submissions/8f1a89f4-0ad6-4ac0-8920-239858dc8666

import Theorems.Thm_Freiman_lower_late_parent_gluing
import Theorems.Thm_Freiman_lower_late_route
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p) : lowerNumericSuccessor t p := by
  exact lower_late_parent_gluing lower_late_route t p hs hb hp97 hlate hc
