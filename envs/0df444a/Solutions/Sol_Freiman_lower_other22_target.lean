-- Prove2me | solution 1 for Freiman.lower_other22_target
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:29.236647+00:00
-- url     : https://prove2.me/submissions/a8018457-7bd5-4bf3-948b-6370d2e9cef0

import Theorems.Thm_Freiman_lower_other22_endpoint_bound
import Theorems.Thm_Freiman_lower_other22_coordinates
import Theorems.Thm_Freiman_lower_other22_parent_lower
import Theorems.Thm_Freiman_lower_other22_priority_upper
import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (t : ℝ) (ht : t ∈ lowerCover Z) (hp : lowerPriority t Z ([2],[3])) :
    lowerLocalLower S ([2],[1]) ≤ lowerLocalCoordinate S t := by
  have hb := lower_other22_endpoint_bound Z B R S h
  rw [lower_other22_coordinates Z B R S h t]
  by_cases hn : lowerEnds Z.1 [3,1]
  · have he : lowerLocalLower S ([2],[1]) ≤ lowerBaseLower Z := by
      simpa only [lowerOther22EndpointBound,if_pos hn] using hb
    exact le_trans he (lower_other22_parent_lower Z t ht)
  · have he : lowerLocalLower S ([2],[1]) ≤ lowerChildUpper Z ([3],[2]) := by
      simpa only [lowerOther22EndpointBound,if_neg hn] using hb
    exact le_trans he (le_of_lt (lower_other22_priority_upper Z B R S h t ht hp hn))
