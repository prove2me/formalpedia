-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_R
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:22:26.704581+00:00
-- url     : https://prove2.me/submissions/c900a2cf-bf7a-4cfe-8f11-7c4e609b829f

-- Exact finite catalog equivalence, with symbolic array-to-list distribution before kernel evaluation.
import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option Elab.async false
private theorem catalog_eq : lowerHistoryCatalogKeys .right = lowerHistoryPathsR.toList.map lowerHistoryPathKey := by
  unfold lowerHistoryCatalogKeys lowerHistoryPaths
  simp only [Array.toList_append,List.filter_append,List.map_append]
  decide +kernel
private theorem generated_eq : (lowerHistoryGeneratedKeys .right).toFinset = (lowerHistoryPathsR.toList.map lowerHistoryPathKey).toFinset := by
  decide +kernel
theorem solution :
    (lowerHistoryGeneratedKeys .right).toFinset = (lowerHistoryCatalogKeys .right).toFinset := by
  rw [catalog_eq]
  exact generated_eq
#print axioms solution
