-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_positive_event_limit_refutes_original_positive_error_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:17:22.839219+00:00
-- url     : https://prove2.me/submissions/3088c15a-b43e-40fc-9909-d796205c6fb4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_cash_gap_excludes_zero_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (hE : 0 < P E)
    (F L : ℕ → Ω → ℝ) (b a : ℝ) (hgap : b < a)
    (hF : ∀ ω ∈ E, Tendsto (fun n => F n ω) atTop (𝓝 a))
    (hL : ∀ ω ∈ E, Tendsto (fun n => L n ω) atTop (𝓝 (0 : ℝ))) :
    ¬ (∀ᵐ ω ∂P,
        Tendsto (fun n => max (F n ω - (b + L n ω)) 0)
          atTop (𝓝 (0 : ℝ))) := by
  intro h
  have hZero : P {ω | ¬ Tendsto
      (fun n => max (F n ω - (b + L n ω)) 0)
          atTop (𝓝 (0 : ℝ))} = 0 := (ae_iff).mp h
  have hSubset : E ⊆ {ω | ¬ Tendsto
      (fun n => max (F n ω - (b + L n ω)) 0)
          atTop (𝓝 (0 : ℝ))} := by
    intro ω hω
    exact AvramDividend.Classical.avram_bvb_obstruction_positive_cash_gap_excludes_zero_limit
      (F · ω) (L · ω) a b (hF ω hω) (hL ω hω) hgap
  have hMeasure : P E ≤ P {ω | ¬ Tendsto
      (fun n => max (F n ω - (b + L n ω)) 0) atTop (𝓝 (0 : ℝ))} :=
    measure_mono hSubset
  rw [hZero] at hMeasure
  exact (not_le_of_gt hE) hMeasure
