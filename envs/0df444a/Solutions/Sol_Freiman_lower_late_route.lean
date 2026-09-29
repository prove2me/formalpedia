-- Prove2me | solution 1 for Freiman.lower_late_route
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:46.770536+00:00
-- url     : https://prove2.me/submissions/b6c29d5f-38c2-4ffd-a058-acd79d1491ac

import Theorems.Thm_Freiman_lower_late_long_route
import Theorems.Thm_Freiman_lower_late_short_route
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p)
    (he : lowerLateEntryDomain p) : ∃ ls : List LowerLabel, lowerLateRouteValid p ls := by
  rcases he hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 with hr | hp
  · exact lower_late_long_route t p hs hd hr
  · exact lower_late_short_route p hp
