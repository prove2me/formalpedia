-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_void_deficit_le_source_first_moment_of_unit_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:04:42.58443+00:00
-- url     : https://prove2.me/submissions/b9a2e60f-a753-4285-9786-5418d803edc1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A unit-sized actual source mark count dominates its occupied event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (hUnit : ∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0 →
      1 ≤ ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))) :
    P {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0} ≤
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ∂P) := by
  classical
  let C : Ω → ENNReal := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let E : Set Ω := {ω | C ω ≠ 0}
  have hZero : MeasurableSet {ω : Ω | C ω = 0} := by
    simpa only [C] using
      (avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
        X s (s + T) (by simp) _ (by measurability))
  have hE : MeasurableSet E := by
    simpa [E, Set.compl_setOf] using hZero.compl
  have hPoint : ∀ ω, E.indicator (fun _ => (1 : ENNReal)) ω ≤ C ω := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa only [Set.indicator_of_mem hω] using
        (hUnit ω (by simpa only [E, C, Set.mem_setOf_eq] using hω))
    · simp only [Set.indicator_of_notMem hω, zero_le]
  calc
    P E = (∫⁻ ω, E.indicator (fun _ => (1 : ENNReal)) ω ∂P) := by
      have hOne : (1 : Ω → ENNReal) = (fun _ : Ω => (1 : ENNReal)) := by
        funext ω
        rfl
      have hInt := lintegral_indicator_one (μ := P) hE
      rw [hOne] at hInt
      exact hInt.symm
    _ ≤ (∫⁻ ω, C ω ∂P) := lintegral_mono hPoint
