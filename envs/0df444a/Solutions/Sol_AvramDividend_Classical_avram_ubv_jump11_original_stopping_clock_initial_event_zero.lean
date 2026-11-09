-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_original_stopping_clock_initial_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T14:37:06.169217+00:00
-- url     : https://prove2.me/submissions/e311ef78-4922-4b0e-97b2-b14fab29e949

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_initial_event_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Stop the original compensated jump counts at a genuine stopping time,
keeping the beginning-of-cell mask predictable in the original filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
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
      (if grid i < τ ω then (1 : ℝ) else 0) *
        ((N i ω).toReal - r i) ∂P) = 0 := by
  classical
  have hEvent (i : ℕ) :
      MeasurableSet[𝓕.rightCont (grid i)] {ω : Ω | grid i < τ ω} := by
    have hBefore : MeasurableSet[𝓕.rightCont (grid i)]
        {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} :=
      hτstop (grid i)
    simpa only [Set.compl_setOf, not_le, WithTop.coe_lt_coe] using hBefore.compl
  let H : ℕ → Ω → ℝ := fun i ω => if grid i < τ ω then 1 else 0
  have hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i) := by
    intro i
    change StronglyMeasurable[𝓕.rightCont (grid i)]
      (fun ω : Ω => if grid i < τ ω then (1 : ℝ) else 0)
    exact (Measurable.ite (hEvent i) measurable_const measurable_const).stronglyMeasurable
  have hBound : ∀ i ω, |H i ω| ≤ (1 : ℝ) := by
    intro i ω
    dsimp [H]
    split_ifs <;> norm_num
  simpa [H] using
    (avram_ubv_jump11_original_finitegrid_initial_event_zero
      X cut grid hGrid H hH 1 hBound n A hA)
