-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_true_bounded_predictable_compensated_fullmark_grid_initial_event_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T17:43:58.619358+00:00
-- url     : https://prove2.me/submissions/92826d40-9e8a-4b5f-b183-cc0e03ff399e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ)
    (A : Set Ω) (hSet : MeasurableSet A)
    (hSetAt : ∀ i, MeasurableSet[𝓕 (grid i)] A)
    (hL0 : 0 ≤ L) :
    MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) 2 P ∧
    (∫ ω in A, (∑ i ∈ Finset.range n, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by
  classical
  have hBase : MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) 2 P :=
    (avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
      X T cut grid hGrid hTime ε hε C hC hBand hCut
      N hActual H hH hHL2 L hL n).1
  refine ⟨hBase, ?_⟩
  let U : ℕ → Ω → ℝ := fun i => A.indicator (H i)
  have hUM (i : ℕ) : StronglyMeasurable[𝓕 (grid i)] (U i) := by
    simpa only [U] using (hH i).indicator (hSetAt i)
  have hUL2 (i : ℕ) : MemLp (U i) 2 P := by
    simpa only [U] using (hHL2 i).indicator hSet
  have hUB (i : ℕ) (ω : Ω) : |U i ω| ≤ L := by
    by_cases hω : ω ∈ A
    · simpa only [U, Set.indicator_of_mem hω] using hL i ω
    · simpa only [U, Set.indicator_of_notMem hω, abs_zero] using hL0
  obtain ⟨hSumL2, hSumZero⟩ :=
    avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
      X T cut grid hGrid hTime ε hε C hC hBand hCut
      N hActual U hUM hUL2 L hUB n
  convert hSumZero using 1
  rw [← integral_indicator hSet]
  congr 1
  funext ω
  by_cases hω : ω ∈ A
  · simp [U, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  · simp [U, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
