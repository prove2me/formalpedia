-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_physical_unbounded_predictable_grid_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:47:57.977034+00:00
-- url     : https://prove2.me/submissions/2ef8eaf3-355a-43c9-9a09-1e25f6a7ad0f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
import Mathlib.Topology.Order.LeftRightLim
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (k : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range k, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range k, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by
  have hCell (i : ℕ) :
      Integrable (fun ω => H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
      (∫ ω, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal) ∂P) = 0 := by
    have h := avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
      X T cut (grid i) (grid (i + 1)) (hGrid i) (hTime (i + 1))
      ε hε (C i) (hC i) (hBand i) (hCut i) (H i) (hH i) (hHL2 i)
    simpa only [hActual i] using h
  have hcells : ∀ i ∈ Finset.range k,
      Integrable (fun ω => H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P := by
    intro i hi
    exact (hCell i).1
  constructor
  · exact integrable_finset_sum _ hcells
  · rw [integral_finset_sum _ hcells]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hCell i).2
