-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:18:08.949452+00:00
-- url     : https://prove2.me/submissions/4f47cf10-c61e-48fd-a1e9-d1616f009969

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_l2_mass_bound_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Discarding finitely many bad grid indices preserves the finite-measure L2 Vitali limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B R : ℝ≥0) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (R : ENNReal))
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by
  have hmShift : ∀ n, AEStronglyMeasurable (Y (n + N)) μ :=
    fun n => hm (n + N)
  have hBShift : ∀ n, eLpNorm (Y (n + N)) 2 μ ≤ (B : ENNReal) := by
    intro n
    exact hB (n + N) (by omega)
  have haeShift : ∀ᵐ ω ∂μ,
      Tendsto (fun n => Y (n + N) ω) atTop (nhds (Z ω)) := by
    filter_upwards [hae] with ω hω
    exact (Filter.tendsto_add_atTop_iff_nat N).2 hω
  obtain ⟨hZ, hMean⟩ :=
    avram_p2_j_ui_finite_measure_l2_mass_bound_expectations
      μ (fun n ω => Y (n + N) ω) Z B R hmShift hBShift hMass haeShift
  exact ⟨hZ, (Filter.tendsto_add_atTop_iff_nat N).1 hMean⟩
