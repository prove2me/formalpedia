-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_original_stopped_predictable_weighted_grid_eventwise_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T15:01:13.412286+00:00
-- url     : https://prove2.me/submissions/28828bf5-1d14-41a0-adb4-a1483387bec0

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_initial_event_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
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
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if grid i < τ ω then H i ω else 0) * ((N i ω).toReal - r i)
    (∫ ω in A, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by
  classical
  have hBefore (i : ℕ) :
      MeasurableSet[𝓕.rightCont (grid i)] {ω : Ω | grid i < τ ω} := by
    have hLe : MeasurableSet[𝓕.rightCont (grid i)]
        {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} :=
      hτstop (grid i)
    have heq :
        {ω : Ω | grid i < τ ω} =
          {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
        WithTop.coe_le_coe, not_le]
    rw [heq]
    exact hLe.compl
  have hMaskStrong (i : ℕ) :
      StronglyMeasurable[𝓕.rightCont (grid i)]
        (fun ω : Ω => if grid i < τ ω then H i ω else 0) := by
    change StronglyMeasurable[𝓕.rightCont (grid i)]
      ({ω : Ω | grid i < τ ω}.indicator (H i))
    exact (hH i).indicator (hBefore i)
  have hMaskBound : ∀ i ω,
      |(if grid i < τ ω then H i ω else (0 : ℝ))| ≤ L := by
    intro i ω
    by_cases hi : grid i < τ ω
    · simpa [hi] using hBound i ω
    · have hL : 0 ≤ L := (abs_nonneg (H i ω)).trans (hBound i ω)
      simpa [hi] using hL
  exact AvramDividend.Classical.avram_ubv_jump11_original_finitegrid_initial_event_zero
    X cut grid hGrid
    (fun i ω => if grid i < τ ω then H i ω else 0)
    hMaskStrong L hMaskBound n A hA
