-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_centered_limit_of_L1_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:10:48.299029+00:00
-- url     : https://prove2.me/submissions/22176b00-5c79-45ef-8d3f-274f393e50e2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Centred truncated compensated jump terms remain centred under actual L¹
convergence. The stochastic L¹ estimate is a separate hypothesis. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMI : Integrable M P)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) = 0)
    (hConv : Tendsto
      (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P)
      atTop (𝓝 0)) :
    (∫ ω, M ω ∂P) = 0 := by
  have hL := tendsto_integral_of_L1 M hMI.aestronglyMeasurable
    (Filter.Eventually.of_forall hFI) hConv
  have hZ : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (∫ ω, M ω ∂P)) := by
    simpa only [hMean] using hL
  exact (tendsto_nhds_unique tendsto_const_nhds hZ).symm
