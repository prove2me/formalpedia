-- Prove2me | solution 1 for Freiman.lagrange_subset_markov
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:06.309963+00:00
-- url     : https://prove2.me/submissions/e26453eb-13e8-4678-9d08-61ad2d35b4da

import Theorems.Thm_Freiman_lagrange_symbolic
import Theorems.Thm_Freiman_markov_symbolic
import Theorems.Thm_Freiman_symbolic_lagrange_subset_markov

open Freiman

theorem solution : lagrangeSpectrum ⊆ markovSpectrum := by
  rw [lagrange_symbolic, markov_symbolic]
  exact symbolic_lagrange_subset_markov

