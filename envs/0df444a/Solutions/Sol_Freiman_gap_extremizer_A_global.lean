-- Prove2me | solution 1 for Freiman.gap_extremizer_A_global
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:05.71304+00:00
-- url     : https://prove2.me/submissions/98480777-dc78-407f-bd34-f69c23988a58

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_extremizer_A_noncentral
import Theorems.Thm_Freiman_gap_endpoint_A_value
import Theorems.Thm_Freiman_gap_threshold_enclosures

open Freiman

theorem solution : (∀ i : ℤ, localValue gapExtremizerA i ≤ gapLeft) ∧ localValue gapExtremizerA 0 = gapLeft := by
  refine ⟨?_, gap_endpoint_A_value⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact le_of_eq gap_endpoint_A_value
  · have h := gap_extremizer_A_noncentral i hi
    have ho := gap_threshold_enclosures
    linarith [ho.1,ho.2.1,ho.2.2.1]
