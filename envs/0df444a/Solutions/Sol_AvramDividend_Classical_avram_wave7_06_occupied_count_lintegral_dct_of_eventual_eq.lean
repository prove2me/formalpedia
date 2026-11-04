-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_occupied_count_lintegral_dct_of_eventual_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:02:45.861207+00:00
-- url     : https://prove2.me/submissions/e05cf334-9ebf-496d-bf15-0b2ca2d53d9e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-- L¹-expectation limit for original occupied marked-time counts dominated by source count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (K : ℕ → Ω → ℝ≥0∞) (N : Ω → ℝ≥0∞)
    (hK : ∀ m, Measurable (K m))
    (hBound : ∀ m ω, K m ω ≤ N ω)
    (hInt : (∫⁻ ω, N ω ∂P) < ⊤)
    (hEvent : ∀ ω, ∀ᶠ m in (Filter.atTop : Filter ℕ), K m ω = N ω) :
    Filter.Tendsto (fun m => ∫⁻ ω, K m ω ∂P)
      Filter.atTop (nhds (∫⁻ ω, N ω ∂P)) := by
  apply MeasureTheory.tendsto_lintegral_of_dominated_convergence N hK ?_ ?_ ?_
  · intro m
    exact Filter.Eventually.of_forall (hBound m)
  · exact ne_of_lt hInt
  · apply Filter.Eventually.of_forall
    intro ω
    have hconst : Filter.Tendsto (fun _ : ℕ => N ω)
        Filter.atTop (nhds (N ω)) := tendsto_const_nhds
    have heq : (fun _ : ℕ => N ω) =ᶠ[Filter.atTop] (fun m => K m ω) := by
      filter_upwards [hEvent ω] with m hm
      exact hm.symm
    exact hconst.congr' heq
