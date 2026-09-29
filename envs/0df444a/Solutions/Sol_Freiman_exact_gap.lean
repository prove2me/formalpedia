-- Prove2me | solution 1 for Freiman.exact_gap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:44:20.568989+00:00
-- url     : https://prove2.me/submissions/3f951e37-aef2-4d98-aa0c-546ba750b15d

import Theorems.Thm_Freiman_gap_symbolic_exact
import Theorems.Thm_Freiman_markov_symbolic

open Freiman

theorem solution : gapLeft ∈ markovSpectrum ∧ cF ∈ markovSpectrum ∧
    (markovSpectrum ∩ Set.Ioo gapLeft cF) = ∅ := by
  rw [markov_symbolic]
  exact gap_symbolic_exact
