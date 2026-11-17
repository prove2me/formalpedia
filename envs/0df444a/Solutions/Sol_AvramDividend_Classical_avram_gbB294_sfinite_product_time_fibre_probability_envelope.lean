-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB294_sfinite_product_time_fibre_probability_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:00:32.14404+00:00
-- url     : https://prove2.me/submissions/2744052c-20d3-4f03-9fb1-8a3c44bf9501

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by
  classical
  calc
    (P.prod volume) S =
        ∫⁻ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ∂volume := by
      exact Measure.prod_apply_symm hS
    _ ≤ ∫⁻ t : ℝ, g t ∂volume := by
      exact lintegral_mono hFibre
