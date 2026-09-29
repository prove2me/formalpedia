-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_X
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:22:27.708434+00:00
-- url     : https://prove2.me/submissions/080a5ce4-8efd-428e-ac5b-5c96b08b2d7b

-- Exact finite catalog equivalence, with symbolic array-to-list distribution before kernel evaluation.
import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option Elab.async false
private theorem catalog_eq : lowerHistoryCatalogKeys .rightMixed = lowerHistoryPathsX.toList.map lowerHistoryPathKey := by
  unfold lowerHistoryCatalogKeys lowerHistoryPaths
  simp only [Array.toList_append,List.filter_append,List.map_append]
  decide +kernel
private theorem generated_eq : (lowerHistoryGeneratedKeys .rightMixed).toFinset = (lowerHistoryPathsX.toList.map lowerHistoryPathKey).toFinset := by
  decide +kernel
theorem solution :
    (lowerHistoryGeneratedKeys .rightMixed).toFinset = (lowerHistoryCatalogKeys .rightMixed).toFinset := by
  rw [catalog_eq]
  exact generated_eq
#print axioms solution
