-- Prove2me | solution 1 for Freiman.middle_interval
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:04.922839+00:00
-- url     : https://prove2.me/submissions/258a218a-3065-41a2-9989-5fb0987ec7a3

import Theorems.Thm_Freiman_middle_controlled_witness
import Theorems.Thm_Freiman_separated_peaks

open Freiman

theorem solution :
    Set.Icc (Real.sqrt 21) (128/25:ℝ) ⊆ lagrangeSpectrum := by
  intro t ht
  obtain ⟨a,ha,hmax,hfinite⟩ := middle_controlled_witness t ht
  exact separated_peaks a t ha hmax hfinite (Or.inl ht.1)
