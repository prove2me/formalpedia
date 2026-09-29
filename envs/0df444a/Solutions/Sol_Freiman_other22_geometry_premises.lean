-- Prove2me | solution 1 for Freiman.other22_geometry_premises
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:13:10.898203+00:00
-- url     : https://prove2.me/submissions/ae4173bc-313f-462c-9223-27c478bb564e

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_lowerHistory_source_dnf_induction
import Theorems.Thm_Freiman_other22_path_shapes
import Theorems.Thm_Freiman_other22_geometry_events

open Freiman

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    ∃ bs ∈ lowerHistorySourcePremises (other22Paths k), lowerHistoryAtBase Z bs := by
  exact lowerHistory_source_dnf_induction Z (other22Paths k) (other22_path_shapes k)
    (other22_geometry_events Z B R S h k hc)
