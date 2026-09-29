-- Prove2me | solution 1 for Freiman.middle_interval_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T19:58:16.792015+00:00
-- url     : https://prove2.me/submissions/86a8f6b3-c076-4702-bd70-47e8be833a3e

import Definitions.Def_Freiman_lagrangeSpectrum
import Definitions.Def_Freiman_gapThreshold
import Theorems.Thm_Freiman_middle_controlled_witness
import Theorems.Thm_Freiman_separated_peaks

open Freiman

theorem solution :
    Set.Icc (Real.sqrt 21) upperRayStart ⊆ lagrangeSpectrum := by
  intro t ht
  have hupper : upperRayStart ≤ (128 / 25 : ℝ) := by
    unfold upperRayStart
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  obtain ⟨a, hcenter, hmax, hfinite⟩ :=
    middle_controlled_witness t ⟨ht.1, le_trans ht.2 hupper⟩
  exact separated_peaks a t hcenter hmax hfinite (Or.inl ht.1)
