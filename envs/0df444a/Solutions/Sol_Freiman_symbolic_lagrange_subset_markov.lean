-- Prove2me | solution 1 for Freiman.symbolic_lagrange_subset_markov
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:52.771901+00:00
-- url     : https://prove2.me/submissions/c467433b-9a1a-4a37-b60e-2a942ba0ff12

import Theorems.Thm_Freiman_attain_limsup_by_shift
import Mathlib.Tactic.Linarith

open Freiman

theorem solution : symbolicLagrangeSpectrum ⊆ symbolicMarkovSpectrum := by
  rintro t ⟨a, ha⟩
  obtain ⟨b, hzero, hbound⟩ := attain_limsup_by_shift a t ha
  refine ⟨b, hbound, ?_⟩
  intro ε hε
  refine ⟨0, ?_⟩
  rw [hzero]
  linarith

