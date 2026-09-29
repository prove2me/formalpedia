-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_lookup
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:24:21.560072+00:00
-- url     : https://prove2.me/submissions/7ff8ad2a-ca16-4d99-98bd-fb35c203f20a

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

theorem solution (hL : (lowerHistoryGeneratedKeys .left).toFinset = (lowerHistoryCatalogKeys .left).toFinset)
    (hR : (lowerHistoryGeneratedKeys .right).toFinset = (lowerHistoryCatalogKeys .right).toFinset)
    (hM : (lowerHistoryGeneratedKeys .mixed).toFinset = (lowerHistoryCatalogKeys .mixed).toFinset)
    (hX : (lowerHistoryGeneratedKeys .rightMixed).toFinset = (lowerHistoryCatalogKeys .rightMixed).toFinset)
    (hH : (lowerHistoryGeneratedKeys .initial).toFinset = (lowerHistoryCatalogKeys .initial).toFinset)
    (p : LowerHistoryPath) (hp : lowerHistoryPathKey p ∈ lowerHistoryGeneratedKeys p.catalog) :
    ∃ p2 ∈ lowerHistoryPaths.toList, lowerHistoryPathKey p2 = lowerHistoryPathKey p := by
  classical
  have hcatalog : (lowerHistoryGeneratedKeys p.catalog).toFinset =
      (lowerHistoryCatalogKeys p.catalog).toFinset := by
    cases p.catalog with
    | left => exact hL
    | right => exact hR
    | mixed => exact hM
    | rightMixed => exact hX
    | initial => exact hH
  have hmem : lowerHistoryPathKey p ∈ lowerHistoryCatalogKeys p.catalog := by
    apply List.mem_toFinset.mp
    rw [← hcatalog]
    exact List.mem_toFinset.mpr hp
  unfold lowerHistoryCatalogKeys at hmem
  obtain ⟨p2, hp2, hkey⟩ := List.mem_map.mp hmem
  exact ⟨p2, (List.mem_filter.mp hp2).1, hkey⟩

#print axioms solution
