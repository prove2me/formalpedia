-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:06:07.285977+00:00
-- url     : https://prove2.me/submissions/2f742c20-bac6-4dc8-98e3-bd95c32413f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i : ℕ, i < n → grid i ≤ grid (i + 1))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ∑ i ∈ Finset.range n,
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
    ∑ i ∈ Finset.range n,
      P {ω : Ω | X.X ((s + grid (i + 1)) - (s + grid i)) ω ∈ B} := by
  classical
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω
  have hXm : ∀ t, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hZm (i : ℕ) : Measurable (Z i) := by
    exact (hXm _).sub (hXm _)
  have hSet (i : ℕ) : MeasurableSet {ω : Ω | Z i ω ∈ B} :=
    hB.preimage (hZm i)
  have hIndicator (i : ℕ) :
      (fun ω : Ω => B.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (Z i ω)) =
        ({ω : Ω | Z i ω ∈ B}).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases hw : Z i ω ∈ B
    · have hwS : ω ∈ {v : Ω | Z i v ∈ B} := hw
      simp [Set.indicator_of_mem hw, Set.indicator_of_mem hwS]
    · have hwS : ω ∉ {v : Ω | Z i v ∈ B} := hw
      simp [Set.indicator_of_notMem hw, Set.indicator_of_notMem hwS]
  have hTerm (i : ℕ) :
      Measurable (fun ω : Ω =>
        B.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (Z i ω)) := by
    rw [hIndicator]
    exact measurable_const.indicator (hSet i)
  have hCell (i : ℕ) (hi : i ∈ Finset.range n) :
      (∫⁻ ω, B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
          (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
        P {ω : Ω | X.X ((s + grid (i + 1)) - (s + grid i)) ω ∈ B} := by
    have hTime : s + grid i ≤ s + grid (i + 1) := by
      have h := add_le_add_left (hGrid i (Finset.mem_range.mp hi)) s
      simpa only [add_comm s] using h
    have hLaw :=
      (X.stationaryIncrements (s + grid i) (s + grid (i + 1)) hTime).measure_mem_eq hB
    have hEvent : P {ω : Ω | Z i ω ∈ B} =
        P {ω : Ω | X.X ((s + grid (i + 1)) - (s + grid i)) ω ∈ B} := by
      simpa only [Z, Set.preimage, Set.mem_setOf_eq] using hLaw
    calc
      (∫⁻ ω, B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
          (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
        ∫⁻ ω, ({ω : Ω | Z i ω ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            exact congrArg (fun f : Ω → ℝ≥0∞ => ∫⁻ ω, f ω ∂P)
              (by simpa only [Z] using hIndicator i)
      _ = P {ω : Ω | Z i ω ∈ B} :=
        MeasureTheory.lintegral_indicator_one (hSet i)
      _ = P {ω : Ω | X.X ((s + grid (i + 1)) - (s + grid i)) ω ∈ B} := hEvent
  calc
    (∫⁻ ω, ∑ i ∈ Finset.range n,
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
      ∑ i ∈ Finset.range n,
        (∫⁻ ω, B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
          (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) := by
            apply MeasureTheory.lintegral_finset_sum
            intro i hi
            exact hTerm i
    _ = ∑ i ∈ Finset.range n,
        P {ω : Ω | X.X ((s + grid (i + 1)) - (s + grid i)) ω ∈ B} := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hCell i hi
