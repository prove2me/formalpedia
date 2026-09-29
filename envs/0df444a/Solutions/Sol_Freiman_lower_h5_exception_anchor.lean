-- Prove2me | solution 1 for Freiman.lower_h5_exception_anchor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:57.133525+00:00
-- url     : https://prove2.me/submissions/cc4f2764-87ec-4e20-ba40-1601b1046068

import Theorems.Thm_Freiman_lower_h5_history_prefix
import Theorems.Thm_Freiman_lower_suffix_target_row2
import Theorems.Thm_Freiman_lower_h5_marked_priority
import Theorems.Thm_Freiman_lower_h5_early_priority
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order
import Theorems.Thm_Freiman_lower_early_geometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_lower_anchor
import Theorems.Thm_Freiman_lower_h5_priority_cover_identity
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lower_h5_local_endpoint_order
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ) (hh : lowerHistory t h n)
    (he : LowerH5PriorityEvent t h n m) : lowerH5LowerBound (h n) t := by
  have hhm := lower_h5_history_prefix t h n m hh (Nat.le_of_lt he.earlier)
  have hstate := hhm.2.1 m (Nat.le_refl m)
  rcases he.branch with ⟨hm,h3,h9,hl,hr,h16⟩
  have hp := he.priority.2 ⟨hm,h3,h9,hl,hr,h16,rfl⟩
  have hhigh : lowerH5LocalUpper (h m) ([2],[2]) < lowerLocalCoordinate (h m) t := by
    by_cases hs : lowerRStar (h m)
    · have hrow := lower_suffix_target_row2 t h m hhm hm h3 hs
      exact lower_h5_marked_priority (h m) t hrow (by simpa only [if_pos hs] using hp)
    · have hd : lowerEarlyDomain (h m) := ⟨hm,h3,h9,hl,hr,h16,hs⟩
      exact lower_h5_early_priority lowerEarlyTerminal_endpoint_order (h m) t hstate hd
        (lower_early_geometry t (h m) hstate hd)
        (lowerEarlyTerminal_lower_anchor t (h m) hstate hd) (by simpa only [if_neg hs] using hp)
  have hid := lower_h5_priority_cover_identity lower_forced_reflections t h n m hh he
  change lowerLocalLower (h n) ([2],[]) ≤ lowerLocalCoordinate (h n) t
  rw [hid.1,hid.2.2]
  exact (lower_h5_local_endpoint_order lowerEarlyTerminal_endpoint_order (h m) ([2],[2])).trans hhigh.le
