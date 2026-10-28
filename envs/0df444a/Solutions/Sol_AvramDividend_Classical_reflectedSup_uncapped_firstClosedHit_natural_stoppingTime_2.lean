-- Prove2me | solution 2 for AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_natural_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:26:54.805097+00:00
-- url     : https://prove2.me/submissions/16337cfc-2f5c-4109-ae60-e034e3df95f5

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_uncapped_firstClosedHit_stopping_and_event

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
        ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω :=
  AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_stopping_and_event X
    (fun n : ℕ => (n : ℝ≥0)) (fun t => exists_nat_gt t) x
