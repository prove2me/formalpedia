-- Prove2me | solution 2 for AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_stopping_and_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:20:18.416656+00:00
-- url     : https://prove2.me/submissions/b5cb8cd9-6ef2-4f1e-8694-f91267485b4d

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_countable_caps_hit_stoppingTime
import Theorems.Thm_AvramDividend_Classical_usc_cofinal_capped_hit_sup_le_iff_level_hit
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  constructor
  · exact reflectedSup_countable_caps_hit_stoppingTime X caps x
  · intro ω t
    exact usc_cofinal_capped_hit_sup_le_iff_level_hit
      (fun u : ℝ≥0 => reflectedSup X u ω)
      caps x
      (fun H => reflectedSup_upperSemicontinuousOn_Icc X ω H)
      hcofinal t
