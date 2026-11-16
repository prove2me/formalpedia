-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB294p_probability_time_fibre_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:19:58.019244+00:00
-- url     : https://prove2.me/submissions/276c21a9-90a0-4b5a-a09f-f227818534ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by
  rw [Measure.prod_apply_symm hS]
  exact lintegral_mono hFibre
