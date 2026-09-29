-- Prove2me | solution 2 for Freiman.lowerHistory_catalog_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T11:34:05.871503+00:00
-- url     : https://prove2.me/submissions/7737c499-0d97-4285-a3f4-593a883e5084

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_raw_descriptor
import Theorems.Thm_Freiman_lowerHistory_structural_generation
import Theorems.Thm_Freiman_lowerHistory_catalog_lookup
import Theorems.Thm_Freiman_lowerHistory_rekey_descriptor
import Theorems.Thm_Freiman_lowerHistory_catalog_shapes
import Theorems.Thm_Freiman_lowerHistory_catalog_L
import Theorems.Thm_Freiman_lowerHistory_catalog_R
import Theorems.Thm_Freiman_lowerHistory_catalog_M
import Theorems.Thm_Freiman_lowerHistory_catalog_X
import Theorems.Thm_Freiman_lowerHistory_catalog_H

open Freiman

-- The raw descriptor supplies a structural path.  The finite catalogue lookup
-- replaces it by a stored row with the same key; rekeying preserves the
-- reached event and the terminal row.
theorem solution :
    ∀ (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ),
      lowerHistory t h n → row ∈ [1,2,3,4] →
      lowerHistoryHazard row (h n) →
      ∃ base p, p ∈ lowerHistoryPaths.toList ∧
        lowerHistoryReached t h n base p ∧ p.row = row := by
  intro t h n row hh hrow haz
  obtain ⟨base, p, hp, hr, hprow⟩ :=
    lowerHistory_raw_descriptor t h n row hh hrow haz
  have hgen : lowerHistoryPathKey p ∈ lowerHistoryGeneratedKeys p.catalog :=
    lowerHistory_structural_generation p hp
  obtain ⟨p2, hp2, hk⟩ := lowerHistory_catalog_lookup
    (by exact lowerHistory_catalog_L)
    (by exact lowerHistory_catalog_R)
    (by exact lowerHistory_catalog_M)
    (by exact lowerHistory_catalog_X)
    (by exact lowerHistory_catalog_H)
    p hgen
  have hp2s : lowerHistoryStructural p2 :=
    lowerHistory_catalog_shapes p2 hp2
  obtain ⟨hr2, hrow2⟩ :=
    lowerHistory_rekey_descriptor t h n base p p2 hp hp2s hk hr
  exact ⟨base, p2, hp2, hr2, hrow2.trans hprow⟩
