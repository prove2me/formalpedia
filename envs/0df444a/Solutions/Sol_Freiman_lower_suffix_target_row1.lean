-- Prove2me | solution 1 for Freiman.lower_suffix_target_row1
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:43.276371+00:00
-- url     : https://prove2.me/submissions/f103e520-9a97-48e6-9c88-276f0d19ee52

import Theorems.Thm_Freiman_lower_other22_reached_target
import Theorems.Thm_Freiman_lower_other22_ancestry
import Theorems.Thm_Freiman_lower_history_certificate_row1
import Theorems.Thm_Freiman_lower_bounded_history
import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    ¬ lowerMixed (h n) → ¬ lowerA (h n) 3 → ¬ lowerA (h n) 9 → lowerLStar (h n) → lowerLocalLower (h n) ([2],[1]) ≤ lowerLocalCoordinate (h n) t := by
  intro hm h3 h9 hl
  classical
  by_cases ho : ∃ m : ℕ, n=m+3 ∧ LowerOther22Geometry (h m) (h (m+1)) (h (m+2)) (h n)
  · rcases ho with ⟨m,rfl,hg⟩
    exact lower_other22_reached_target t _ (lower_other22_ancestry t h m hh hg)
  · exact lower_history_certificate_row1 t h n hh (lower_bounded_history t h n hh) hm h3 h9 hl
