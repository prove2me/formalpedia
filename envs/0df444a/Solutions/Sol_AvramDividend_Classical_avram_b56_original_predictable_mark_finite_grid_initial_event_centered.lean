-- Prove2me | solution 1 for AvramDividend.Classical.avram_b56_original_predictable_mark_finite_grid_initial_event_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:20:44.791096+00:00
-- url     : https://prove2.me/submissions/3f2f728d-8afe-4e5f-8fc7-c51cee2dac4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b55_original_predictable_mark_cell_initial_event_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical negative marked-jump predictable finite grid has zero expected gain on a past event. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (S : Finset ι) (cut : ι → ℕ)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (htT : ∀ i ∈ S, t i ≤ T)
    (ε : ι → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-(ε i)))
    (hCut : ∀ i ∈ S,
      B i ⊆ Iic (-(1 / ((cut i : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (H i))
    (hHL2 : ∀ i ∈ S, MemLp (H i) 2 P)
    (A : Set Ω)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] A) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : ι → Ω → ℝ≥0∞ := fun i ω =>
      NX ω (Ioc (s i) (t i) ×ˢ B i)
    let r : ι → ℝ := fun i =>
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ S, H i ω * ((N i ω).toReal - r i)
    Integrable F P ∧ (∫ ω in A, F ω ∂P) = 0 := by 
  classical
  dsimp only
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N : ι → Ω → ℝ≥0∞ := fun i ω =>
    NX ω (Ioc (s i) (t i) ×ˢ B i)
  let r : ι → ℝ := fun i =>
    (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
  let cell : ι → Ω → ℝ := fun i ω =>
    H i ω * ((N i ω).toReal - r i)
  have hc (i : ι) (hi : i ∈ S) :
      Integrable (cell i) P ∧
      (∫ ω in A, cell i ω ∂P) = 0 :=
    avram_b55_original_predictable_mark_cell_initial_event_mean_zero
      X T (cut i) (s i) (t i) (hst i hi) (htT i hi)
      (ε i) (hε i hi) (B i) (hB i hi)
      (hBand i hi) (hCut i hi)
      (H i) (hH i hi) (hHL2 i hi) A (hA i hi)
  constructor
  · exact integrable_finset_sum S (fun i hi => (hc i hi).1)
  · rw [integral_finset_sum S (fun i hi => (hc i hi).1.integrableOn)]
    exact Finset.sum_eq_zero (fun i hi => (hc i hi).2)
