-- Prove2me | solution 1 for Freiman.other22_geometry_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:13:10.923421+00:00
-- url     : https://prove2.me/submissions/f2c3490c-d312-4218-906a-c85f50459deb

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_other22_represented_order
import Theorems.Thm_Freiman_other22_anchor_represented
import Theorems.Thm_Freiman_other22_residual_represented
import Theorems.Thm_Freiman_other22_valid_comparisons
import Theorems.Thm_Freiman_other22_geometry_premises
import Theorems.Thm_Freiman_other22_context_rectangle
import Theorems.Thm_Freiman_other22_endpoint_inventory

open Freiman

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerLocalLower S ([2],[1]) ≤ other22AnchorValue Z := by
  apply other22_represented_order Z (other22Context k) hc
    (other22Ancestor k) other22ResidualWords (other22AncestorUpper k) false
    (other22AnchorValue Z) (lowerLocalLower S ([2],[1]))
    (other22_anchor_represented Z B R S h k hc)
    (other22_residual_represented Z B R S h k hc)
  have hcs := other22_valid_comparisons k (lowerRatio Z.1) (lowerRatio Z.2) (lowerScale Z)
    (other22_context_rectangle Z B R S h k hc) (other22_geometry_premises Z B R S h k hc)
  unfold lowerHistoryComparisonsHold at hcs
  rw [other22_endpoint_inventory k] at hcs
  exact hcs
