-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_canonical_positivepart_remainder_L1_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:29:22.207205+00:00
-- url     : https://prove2.me/submissions/a2192579-bddb-4f74-8b05-12869ef4b2c8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Err B : ℕ → Ω → ℝ)
    (hErr : ∀ m, Integrable (Err m) μ)
    (hB : ∀ m, Integrable (B m) μ)
    (hPosLim : Tendsto (fun m =>
      ∫ ω, max (Err m ω - B m ω) (0 : ℝ) ∂μ) atTop (nhds (0 : ℝ))) :
    ∃ R : ℕ → Ω → ℝ,
      (∀ m, Integrable (R m) μ) ∧
      (∀ m, ∀ᵐ ω ∂μ, 0 ≤ R m ω) ∧
      Tendsto (fun m => ∫ ω, R m ω ∂μ) atTop (nhds (0 : ℝ)) ∧
      (∀ m, ∀ᵐ ω ∂μ, Err m ω ≤ B m ω + R m ω) := by
  refine ⟨fun m ω => max (Err m ω - B m ω) 0, ?_, ?_, hPosLim, ?_⟩
  · intro m
    exact ((hErr m).sub (hB m)).pos_part
  · intro m
    exact ae_of_all μ (fun ω => le_max_right _ _)
  · intro m
    exact ae_of_all μ (fun ω => by
      have h := le_max_left (Err m ω - B m ω) (0 : ℝ)
      linarith)
