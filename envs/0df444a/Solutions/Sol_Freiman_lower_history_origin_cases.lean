-- Prove2me | solution 1 for Freiman.lower_history_origin_cases
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:03.812988+00:00
-- url     : https://prove2.me/submissions/8cc367f7-3a43-48a4-98a1-9b9e57a50083

import Theorems.Thm_Freiman_lower_bounded_history
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) (right : Bool)
    (hm : lowerEnds (lowerSide (lowerPhysicalPath h n) right) [3,1,3,1]) :
    lowerInitialMarked h n right ∨ lowerGenericMarked h n right := by
  have hb := lower_bounded_history t h n hh
  rcases hb right hm with ⟨m,hmn,hseven,hbirth,hpersist⟩
  rcases hbirth with rfl | ⟨hm0,hbirth,hmarked⟩
  · exact Or.inl ⟨by simpa using hseven, fun j hj => hpersist j (Nat.zero_le j) hj⟩
  · exact Or.inr ⟨m,hm0,hmn,hseven,hbirth,hmarked,hpersist⟩
