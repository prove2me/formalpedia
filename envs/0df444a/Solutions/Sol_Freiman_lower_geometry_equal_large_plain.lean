-- Prove2me | solution 1 for Freiman.lower_geometry_equal_large_plain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:40.473063+00:00
-- url     : https://prove2.me/submissions/33cb3b59-0a7b-4d5e-ab4c-e205d76db147

import Theorems.Thm_Freiman_lower_geometry_equal_large_plain_with_run
import Theorems.Thm_Freiman_lower_run_family
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ ¬ lowerL p) : lowerNumericSuccessor t p := by
  exact lower_geometry_equal_large_plain_with_run lower_run_family t p hs hb hp97 hlate hc
