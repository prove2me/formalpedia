-- Prove2me | solution 1 for Freiman.lower_generic_suffix_birth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:22.336648+00:00
-- url     : https://prove2.me/submissions/96820c3f-5d29-4499-a2af-9c45b4b4cbbe

import Theorems.Thm_Freiman_lower_guard_offered
import Theorems.Thm_Freiman_lower_guard_checks
import Theorems.Thm_Freiman_lower_guard_case_birth313
import Theorems.Thm_Freiman_lower_guard_run_birth313
import Definitions.Def_Freiman_lowerWordGuardData

open Freiman
theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (l : LowerLabel) (hl : lowerOffered (h n) l) (right : Bool)
    (hnew : lowerEnds (lowerSide (lowerChild (h n) l) right) [3,1,3])
    (hchanged : lowerSide (lowerChild (h n) l) right ≠ lowerSide (lowerNormalize (h n)) right) :
    l = ([2],[3]) := by
  have hp := (hh.2.1 n (Nat.le_refl n)).1
  rcases lower_guard_offered (h n) hp l hl with ⟨c,hc,hf,hm⟩ | ⟨hr,k,hk,rfl⟩
  · exact lower_guard_case_birth313 (h n) c (lower_guard_checks c hc) hf l hm right hnew hchanged
  · exact False.elim (lower_guard_run_birth313 (h n) k hk right hnew)
