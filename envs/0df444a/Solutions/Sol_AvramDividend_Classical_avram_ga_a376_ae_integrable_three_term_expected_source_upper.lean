-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a376_ae_integrable_three_term_expected_source_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:32:17.459515+00:00
-- url     : https://prove2.me/submissions/7f6b4146-098e-42c3-9628-64c1cbe15065

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F E A B : Ω → ℝ) (ε : ℝ)
    (hFI : Integrable F P)
    (hEI : Integrable E P)
    (hAI : Integrable A P)
    (hBI : Integrable B P)
    (hPt : ∀ᵐ ω ∂P, F ω ≤ ε*E ω+A ω+B ω) :
    (∫ ω, F ω ∂P) ≤
      ε*(∫ ω, E ω ∂P) +
        (∫ ω, A ω ∂P) +
        (∫ ω, B ω ∂P) := by
  have hEI' := hEI.const_mul ε
  have hMA := hEI'.add hAI
  have hM := hMA.add hBI
  calc
    (∫ ω, F ω ∂P) ≤ ∫ ω, ε*E ω+A ω+B ω ∂P :=
      integral_mono_ae hFI hM hPt
    _ = (∫ ω, ε*E ω+A ω ∂P) +
          (∫ ω, B ω ∂P) := by
      exact integral_add hMA hBI
    _ = ((∫ ω, ε*E ω ∂P)+(∫ ω, A ω ∂P)) +
          (∫ ω, B ω ∂P) := by
      rw [integral_add hEI' hAI]
    _ = ε*(∫ ω, E ω ∂P)+(∫ ω, A ω ∂P)+
          (∫ ω, B ω ∂P) := by
      rw [integral_const_mul]
