-- Prove2me | solution 1 for Freiman.lower_geometry_equal_early
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:46.648975+00:00
-- url     : https://prove2.me/submissions/1fd8c5e2-8836-4314-a78a-c9be73d95f00

import Theorems.Thm_Freiman_lower_early_parent_gluing
import Theorems.Thm_Freiman_lower_early_geometry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ lowerR p ∧ ¬ lowerA p 16) : lowerNumericSuccessor t p := by
  exact lower_early_parent_gluing lower_early_geometry t p hs hb hp97 hlate hc
