-- Prove2me | solution 1 for Freiman.lower_geometry_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:20.578996+00:00
-- url     : https://prove2.me/submissions/9a608a37-31cd-46a6-8102-2267105a4d0d

import Theorems.Thm_Freiman_lower_geometry_mixed_open
import Theorems.Thm_Freiman_lower_geometry_mixed_p97
import Theorems.Thm_Freiman_lower_geometry_mixed_three
import Theorems.Thm_Freiman_lower_geometry_mixed_long
import Theorems.Thm_Freiman_lower_geometry_equal_open
import Theorems.Thm_Freiman_lower_geometry_equal_small_left
import Theorems.Thm_Freiman_lower_geometry_equal_small_plain
import Theorems.Thm_Freiman_lower_geometry_equal_early
import Theorems.Thm_Freiman_lower_geometry_equal_large_left
import Theorems.Thm_Freiman_lower_geometry_equal_large_plain
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p) : lowerNumericSuccessor t p := by
  by_cases hm : lowerMixed p
  · by_cases h2 : lowerH p 2
    · exact lower_geometry_mixed_open t p hs hb hp97 hlate ⟨hm,h2⟩
    · by_cases h5 : lowerH p 5
      · by_cases hl : lowerL p
        · exact lower_geometry_mixed_p97 t p hs hb hp97 hlate ⟨hm,h2,h5,hl⟩
        · exact lower_geometry_mixed_three t p hs hb hp97 hlate ⟨hm,h2,h5,hl⟩
      · exact lower_geometry_mixed_long t p hs hb hp97 hlate ⟨hm,h2,h5⟩
  · by_cases h3 : lowerA p 3
    · exact lower_geometry_equal_open t p hs hb hp97 hlate ⟨hm,h3⟩
    · by_cases h9 : lowerA p 9
      · by_cases hl : lowerL p
        · exact lower_geometry_equal_small_left t p hs hb hp97 hlate ⟨hm,h3,h9,hl⟩
        · by_cases hr : ¬ lowerR p ∨ lowerA p 16
          · exact lower_geometry_equal_small_plain t p hs hb hp97 hlate ⟨hm,h3,h9,hl,hr⟩
          · push_neg at hr
            exact lower_geometry_equal_early t p hs hb hp97 hlate ⟨hm,h3,h9,hl,hr.1,hr.2⟩
      · by_cases hl : lowerL p
        · exact lower_geometry_equal_large_left t p hs hb hp97 hlate ⟨hm,h3,h9,hl⟩
        · exact lower_geometry_equal_large_plain t p hs hb hp97 hlate ⟨hm,h3,h9,hl⟩
