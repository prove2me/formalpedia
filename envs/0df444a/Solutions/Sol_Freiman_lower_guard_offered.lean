-- Prove2me | solution 1 for Freiman.lower_guard_offered
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:22.326559+00:00
-- url     : https://prove2.me/submissions/230ba8c9-dc99-4721-bcd4-162fa7314dbb

import Theorems.Thm_Freiman_lower_guard_source_mixed
import Theorems.Thm_Freiman_lower_guard_source_equal
import Theorems.Thm_Freiman_lower_guard_source_run
import Definitions.Def_Freiman_lowerWordGuardData

open Freiman
theorem solution (p : LowerPair) (hp : lowerAdmissible p) (l : LowerLabel) (hl : lowerOffered p l) : lowerGuardAllowed p l := by
  rcases hl with hl | ⟨hr,k,hk,rfl⟩
  · left
    by_cases hm : lowerMixed p
    · exact lower_guard_source_mixed p hp hm l (by simpa only [if_pos hm] using hl)
    · exact lower_guard_source_equal p hp hm l (by simpa only [if_neg hm] using hl)
  · by_cases hs : k < 3
    · exact Or.inl (lower_guard_source_run p hp hr k hk hs)
    · exact Or.inr ⟨hr,k,Nat.le_of_not_gt hs,rfl⟩
