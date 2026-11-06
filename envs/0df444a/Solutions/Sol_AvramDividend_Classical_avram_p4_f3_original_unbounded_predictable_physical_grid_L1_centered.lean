-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_physical_grid_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:16:09.854006+00:00
-- url     : https://prove2.me/submissions/27787a66-c198-4cec-995b-c844bb4d2c34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- An actual finite predictable marked jump grid has an integrable zero-mean source sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (n : ℕ) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i)
    let r : ℕ → ℝ := fun i =>
      ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal
    Integrable (fun ω => ∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal - r i)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal - r i)) ∂P) = 0 := by
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (grid i) (grid (i + 1)) ×ˢ B i)
  let r : ℕ → ℝ := fun i =>
    ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal
  change Integrable (fun ω => ∑ i ∈ Finset.range n,
    H i ω * ((N i ω).toReal - r i)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal - r i)) ∂P) = 0
  have hCell (i : ℕ) :
      Integrable (fun ω => H i ω * ((N i ω).toReal - r i)) P ∧
      (∫ ω, H i ω * ((N i ω).toReal - r i) ∂P) = 0 := by
    exact avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
      X T cut (grid i) (grid (i + 1)) (hGrid i) (hTime (i + 1))
      ε hε (B i) (hB i) (hBand i) (hCut i) (H i) (hH i) (hHL2 i)
  have hInt : ∀ i ∈ Finset.range n,
      Integrable (fun ω => H i ω * ((N i ω).toReal - r i)) P := by
    intro i hi
    exact (hCell i).1
  constructor
  · exact integrable_finset_sum (Finset.range n) hInt
  · rw [integral_finset_sum (Finset.range n) hInt]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hCell i).2
