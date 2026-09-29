-- Prove2me | solution 1 for Freiman.late_route_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:45.808708+00:00
-- url     : https://prove2.me/submissions/555db286-5ef4-4190-a3b4-3e0aab988390

import Theorems.Thm_Freiman_late_all_paths
import Theorems.Thm_Freiman_late_route_from_checks
import Theorems.Thm_Freiman_late_normalizations_transfer
import Theorems.Thm_Freiman_late_checks_transfer
import Theorems.Thm_Freiman_late_all_endpoints
import Theorems.Thm_Freiman_late_fork_endpoints
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution (p : LowerPair) (i : ℕ) (hi : lateIndex i lateCatalog.paths.size)
    (hm : lateMatches p (latePath lateCatalog i).right3)
    (hr : lateHolds (lateBounds lateCatalog (latePath lateCatalog i).required) (lateR p) (lateS p) (lateQ p))
    (ha : lowerGood (lowerChild p ([2],[2])) ∧ lowerGood (lowerChild p ([2],[1]))) :
    lowerLateRouteValid p (latePath lateCatalog i).route := by
  have hv := late_all_paths i hi
  have hn := late_normalizations_transfer p (latePath lateCatalog i) hv hr
  exact late_route_from_checks lowerEarlyTerminal_endpoint_order p (latePath lateCatalog i) hm.1 hv ha hn
    (late_fork_endpoints p (latePath lateCatalog i) hm hv hn)
    (late_checks_transfer p i hi hm hv late_all_endpoints hr)
