-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_stopping_and_event
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:19:36.363523+00:00
-- url     : https://prove2.me/submissions/56308f01-f718-49c7-a59d-e81ed72272aa

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_countable_caps_hit_stoppingTime
import Theorems.Thm_AvramDividend_Classical_usc_cofinal_capped_hit_sup_le_iff_level_hit
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (caps : ℕ → ℝ≥0)
    (hcofinal : ∀ t : ℝ≥0, ∃ n : ℕ, t < caps n)
    (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (caps n) ∩
          (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {caps n}))) ∧
    ∀ ω : Ω, ∀ t : ℝ≥0,
      (⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (caps n) ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {caps n}))) ≤
          (t : WithTop ℝ≥0) ↔
        ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω := by
  exact ⟨reflectedSup_countable_caps_hit_stoppingTime X caps x, fun ω t =>
    usc_cofinal_capped_hit_sup_le_iff_level_hit (fun u : ℝ≥0 => reflectedSup X u ω) caps x
      (fun H => reflectedSup_upperSemicontinuousOn_Icc X ω H) hcofinal t⟩
