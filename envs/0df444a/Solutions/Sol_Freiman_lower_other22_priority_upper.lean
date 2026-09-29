-- Prove2me | solution 1 for Freiman.lower_other22_priority_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:29.037765+00:00
-- url     : https://prove2.me/submissions/c6042f23-8de1-412c-ab41-2ee5bc1ce67c

import Theorems.Thm_Freiman_lower_other22_exclusion_upper
import Theorems.Thm_Freiman_lower_other22_priority_lower
import Theorems.Thm_Freiman_lower_other22_parent_lower
import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (t : ℝ) (ht : t ∈ lowerCover Z) (hp : lowerPriority t Z ([2],[3]))
    (hn : ¬ lowerEnds Z.1 [3,1]) : lowerChildUpper Z ([3],[2]) < lowerLocalCoordinate Z t := by
  have hm : ¬ lowerMixed Z := by
    exact fun hn => hn h.equalZ
  have hl : ¬ lowerL Z := by simpa only [lowerL,h.normalizedZ] using hn
  have hnot := hp.1 ⟨hm,h.largeZ3,h.largeZ9,hl,rfl⟩
  exact lower_other22_exclusion_upper Z t hnot
    (lt_of_lt_of_le (lower_other22_priority_lower Z B R S h hn) (lower_other22_parent_lower Z t ht))
