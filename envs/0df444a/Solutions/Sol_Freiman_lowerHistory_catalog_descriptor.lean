-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:15.635838+00:00
-- url     : https://prove2.me/submissions/3deea1d4-861f-46b6-b174-11576211af44

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

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n)) :
    ∃ base p, p ∈ lowerHistoryPaths.toList ∧ lowerHistoryReached t h n base p ∧ p.row = row := by
  obtain ⟨base,p,hp,hr,hrowp⟩ := lowerHistory_raw_descriptor t h n row hh hrow haz
  obtain ⟨p2,hmem,hkey⟩ := lowerHistory_catalog_lookup lowerHistory_catalog_L lowerHistory_catalog_R
    lowerHistory_catalog_M lowerHistory_catalog_X lowerHistory_catalog_H p (lowerHistory_structural_generation p hp)
  have ht := lowerHistory_rekey_descriptor t h n base p p2 hp (lowerHistory_catalog_shapes p2 hmem) hkey hr
  exact ⟨base,p2,hmem,ht.1,ht.2.trans hrowp⟩
