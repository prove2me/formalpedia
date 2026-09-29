-- Prove2me | solution 1 for Freiman.gap_extremizer_B_global
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:05.592296+00:00
-- url     : https://prove2.me/submissions/da7c2ddc-00e8-4f1c-b58e-df934cdf00ec

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_extremizer_B_noncentral
import Theorems.Thm_Freiman_gap_endpoint_B_value
import Theorems.Thm_Freiman_gap_threshold_enclosures

open Freiman

theorem solution : (∀ i : ℤ, localValue gapExtremizerB i ≤ cF) ∧ localValue gapExtremizerB 0 = cF := by
  refine ⟨?_, gap_endpoint_B_value⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact le_of_eq gap_endpoint_B_value
  · have h := gap_extremizer_B_noncentral i hi
    have ho := gap_threshold_enclosures
    linarith [ho.1,ho.2.1,ho.2.2.1]
