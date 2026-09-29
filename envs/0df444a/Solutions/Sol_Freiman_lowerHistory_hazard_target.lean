-- Prove2me | solution 1 for Freiman.lowerHistory_hazard_target
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:28.430988+00:00
-- url     : https://prove2.me/submissions/b38faeaa-42f9-450f-94d5-659b9a47b1b0

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_catalog_descriptor
import Theorems.Thm_Freiman_lowerHistory_catalog_shapes
import Theorems.Thm_Freiman_lowerHistory_catalog_target

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n)) :
    lowerHistoryTarget row (h n) t := by
  obtain ⟨base,p,hmem,hr,hpr⟩ := lowerHistory_catalog_descriptor t h n row hh hrow haz
  have ht := lowerHistory_catalog_target t h n hh base p (lowerHistory_catalog_shapes p hmem) hr hmem (by simpa [hpr] using haz)
  simpa [hpr] using ht
