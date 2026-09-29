-- Prove2me | solution 1 for Freiman.lower_p97_target
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:14.806869+00:00
-- url     : https://prove2.me/submissions/9dea1a9a-449a-440e-927d-29ee8dbcae40

import Theorems.Thm_Freiman_lower_h5_active_anchor
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) : lowerP97Anchor (h n) t := by
  intro hm h2 h5 hl
  exact lower_h5_active_anchor t h n hh ⟨hm,h2,h5,hl⟩
