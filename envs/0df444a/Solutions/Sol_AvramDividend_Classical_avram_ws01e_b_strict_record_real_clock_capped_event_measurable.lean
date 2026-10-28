-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_strict_record_real_clock_capped_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:09:42.188901+00:00
-- url     : https://prove2.me/submissions/038fc979-2b26-430a-922d-ad82e1265826

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (clock : Θ → ℝ) (hc : Measurable clock)
    (n : ℕ) :
    MeasurableSet {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} := by
  have hL : Measurable (fun z : Ω × Θ => τ z.1) :=
    hτ.comp measurable_fst
  have hCR : Measurable
      (fun z : Ω × Θ => Real.toNNReal (clock z.2)) :=
    (hc.comp measurable_snd).real_toNNReal
  have hR : Measurable
      (fun z : Ω × Θ => (Real.toNNReal (clock z.2) : ℝ≥0∞)) :=
    hCR.coe_nnreal_ennreal
  exact (measurableSet_lt hL measurable_const).inter
    (measurableSet_lt hL hR)
