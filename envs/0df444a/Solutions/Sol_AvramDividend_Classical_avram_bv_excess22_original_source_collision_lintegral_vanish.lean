-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess22_original_source_collision_lintegral_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:40:15.405756+00:00
-- url     : https://prove2.me/submissions/f11ebd66-ebd5-4100-9481-451054033f2c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Source finite-jump collision mass decays on genuinely refining occupied-cell grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ → Ω → ℝ≥0∞) (N : Ω → ℝ≥0∞)
    (hDiffMeas : ∀ m, Measurable (fun ω => N ω - K m ω))
    (hInt : (∫⁻ ω, N ω ∂P) < ⊤)
    (hEvent : ∀ᵐ ω ∂P, ∀ᶠ m in (Filter.atTop : Filter ℕ),
      K m ω = N ω) :
    Filter.Tendsto (fun m => ∫⁻ ω, N ω - K m ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hlim : Filter.Tendsto
      (fun m => ∫⁻ ω, N ω - K m ω ∂P) Filter.atTop
      (nhds (∫⁻ ω, (0 : ℝ≥0∞) ∂P)) := by
    apply MeasureTheory.tendsto_lintegral_of_dominated_convergence N hDiffMeas
    · intro m
      exact Filter.Eventually.of_forall (fun ω => tsub_le_self)
    · exact ne_of_lt hInt
    · filter_upwards [hEvent] with ω hω
      have heq : (fun _ : ℕ => (0 : ℝ≥0∞)) =ᶠ[Filter.atTop]
          (fun m => N ω - K m ω) := by
        filter_upwards [hω] with m hm
        simp [hm]
      exact tendsto_const_nhds.congr' heq
  simpa using hlim
