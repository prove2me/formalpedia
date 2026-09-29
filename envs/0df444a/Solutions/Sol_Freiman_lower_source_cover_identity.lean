-- Prove2me | solution 1 for Freiman.lower_source_cover_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:03.828155+00:00
-- url     : https://prove2.me/submissions/6c8cbbcc-276c-4ef9-a682-fcfaeaef53c3

import Theorems.Thm_Freiman_lower_auxiliary_width
import Definitions.Def_Freiman_lowerSourceCover
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (p : LowerPair) : lowerSourceCover p = lowerCover p := by
  classical
  have hw : ∀ w e : List ℕ+, lowerSourceAuxWidth w e = lowerWidth (w++e) := by
    intro w e
    by_cases he : e = [1,3]
    · subst e
      simpa [lowerSourceAuxWidth] using lower_auxiliary_width w
    · simp only [lowerSourceAuxWidth, if_neg he]
  have he : lowerSourceEqualWords = lowerEqualWords := by
    funext p upper
    simp only [lowerSourceEqualWords, lowerEqualWords, hw]
  have hp : lowerSourceEndpointWords = lowerEndpointWords := by
    funext p upper
    simp only [lowerSourceEndpointWords, lowerEndpointWords, he]
  simp only [lowerSourceCover, lowerCover, lowerSourceEndpoint, lowerEndpoint, hp]
