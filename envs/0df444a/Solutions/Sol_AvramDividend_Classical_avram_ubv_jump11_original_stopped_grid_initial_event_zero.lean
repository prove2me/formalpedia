-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_original_stopped_grid_initial_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T14:30:00.524518+00:00
-- url     : https://prove2.me/submissions/e426886c-2e8c-4fa2-8688-9c3156f92e7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_initial_event_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- A bounded predictable stopping mask preserves the original finite-grid
compensated physical negative-jump count's initial-event mean zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (K : Ω → ℕ)
    (hK : ∀ i, MeasurableSet[𝓕.rightCont (grid i)] {ω : Ω | i < K ω})
    (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω in A, ∑ i ∈ Finset.range n,
      (if i < K ω then (1 : ℝ) else 0) * ((N i ω).toReal - r i) ∂P) = 0 := by
  classical
  let H : ℕ → Ω → ℝ := fun i ω => if i < K ω then 1 else 0
  have hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i) := by
    intro i
    change StronglyMeasurable[𝓕.rightCont (grid i)]
      (fun ω : Ω => if i < K ω then (1 : ℝ) else 0)
    exact (Measurable.ite (hK i) measurable_const measurable_const).stronglyMeasurable
  have hBound : ∀ i ω, |H i ω| ≤ (1 : ℝ) := by
    intro i ω
    dsimp [H]
    split_ifs <;> norm_num
  simpa [H] using
    (avram_ubv_jump11_original_finitegrid_initial_event_zero
      X cut grid hGrid H hH 1 hBound n A hA)
