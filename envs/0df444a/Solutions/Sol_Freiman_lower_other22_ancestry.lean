-- Prove2me | solution 1 for Freiman.lower_other22_ancestry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:43.148042+00:00
-- url     : https://prove2.me/submissions/d0ae0830-14bb-46cc-8b69-8c871946f3ed

import Theorems.Thm_Freiman_lower_other22_birth_priority
import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (m : ℕ)
    (hh : lowerHistory t h (m+3))
    (hg : LowerOther22Geometry (h m) (h (m+1)) (h (m+2)) (h (m+3))) :
    lowerOther22Reached t (h (m+3)) := by
  exact ⟨h m,h (m+1),h (m+2),hg,((hh.2.1 m (by omega)).2.2.1),
    lower_other22_birth_priority t h m hh hg⟩
