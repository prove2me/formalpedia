-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_capped_closedLevelHit_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T22:55:02.472353+00:00
-- url     : https://prove2.me/submissions/91b86dfe-6b8d-4ab2-908d-fb6182fcea24

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_exists_countable_dense_nnreal_time_set_zero
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_isStoppingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}))) := by
  obtain ⟨S, hS, hDense, h0⟩ :=
    exists_countable_dense_nnreal_time_set_zero
  exact reflectedSup_capped_firstClosedHit_isStoppingTime
    X S hS hDense h0 H x
