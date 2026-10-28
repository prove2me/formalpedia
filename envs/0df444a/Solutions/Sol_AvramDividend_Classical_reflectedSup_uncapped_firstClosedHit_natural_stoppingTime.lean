-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_natural_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:25:43.840949+00:00
-- url     : https://prove2.me/submissions/30c6dcb4-309e-4d71-b637-4a18fc64b7f8

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_uncapped_firstClosedHit_stopping_and_event
import Theorems.Thm_AvramDividend_Classical_nnreal_natCaps_cofinal

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (n : ℝ≥0) ∩
          (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {(n : ℝ≥0)}))) ∧
    ∀ ω : Ω, ∀ t : ℝ≥0,
      (⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (n : ℝ≥0) ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {(n : ℝ≥0)}))) ≤
          (t : WithTop ℝ≥0) ↔
        ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω := by
  exact reflectedSup_uncapped_firstClosedHit_stopping_and_event X (fun n : ℕ => (n : ℝ≥0))
    nnreal_natCaps_cofinal x
