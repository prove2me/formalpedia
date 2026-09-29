-- Prove2me | solution 1 for Freiman.lower_h5_initial_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:57.590536+00:00
-- url     : https://prove2.me/submissions/48982d9b-4af1-4955-9fb0-430c552eef67

import Theorems.Thm_Freiman_lower_h5_initial_fixed
import Theorems.Thm_Freiman_lower_h5_initial_entry
import Theorems.Thm_Freiman_lower_entry_family_context
import Theorems.Thm_Freiman_lower_entry_family_domain
import Theorems.Thm_Freiman_lower_h5_initial_bridges
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution (t : ℝ) (p : LowerPair) (hp : lowerInitialRoot t p) : ¬(lowerMixed p ∧ lowerL p) := by
  rcases hp with hfix | ⟨f,n,k,v,hselected,hroot⟩
  · exact lower_h5_initial_fixed p hfix
  · rcases hroot with ⟨l,hl,rfl,hsafe⟩ | ⟨hk,d,hd,rfl⟩
    · exact lower_h5_initial_entry lower_entry_family_context lower_entry_family_domain f n k v l hl
    · subst k
      exact lower_h5_initial_bridges f n v d hd
