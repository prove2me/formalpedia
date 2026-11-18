-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_sfinite_product_time_fibre_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:06:20.16893+00:00
-- url     : https://prove2.me/submissions/bc3607ca-05fb-489a-bd82-ea8f2c81060c

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section
/-- Exact source Fubini product time-fibre domination under SFinite. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by
  rw [Measure.prod_apply_symm hS]
  exact lintegral_mono hFibre
