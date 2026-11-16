-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_positive_event_pathwise_nonconvergence_refutes_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:55:54.501008+00:00
-- url     : https://prove2.me/submissions/aadefc0b-b20e-4aa6-bafd-c45ca5d454c9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (hE : 0 < P E)
    (F : ℕ → Ω → ℝ)
    (hNonconvergence : ∀ ω ∈ E,
      ¬ Tendsto (fun n => max (F n ω) 0)
        atTop (𝓝 (0 : ℝ))) :
    ¬ (∀ᵐ ω ∂P,
      Tendsto (fun n => max (F n ω) 0)
        atTop (𝓝 (0 : ℝ))) := by
  intro hAe
  have hZero : P {ω | ¬ Tendsto (fun n => max (F n ω) 0)
      atTop (𝓝 (0 : ℝ))} = 0 := (ae_iff).mp hAe
  have hSubset : E ⊆ {ω | ¬ Tendsto (fun n => max (F n ω) 0)
      atTop (𝓝 (0 : ℝ))} := by
    intro ω hMem
    exact hNonconvergence ω hMem
  have hMono : P E ≤ P {ω | ¬ Tendsto (fun n => max (F n ω) 0)
      atTop (𝓝 (0 : ℝ))} := measure_mono hSubset
  rw [hZero] at hMono
  exact (not_le_of_gt hE) hMono
