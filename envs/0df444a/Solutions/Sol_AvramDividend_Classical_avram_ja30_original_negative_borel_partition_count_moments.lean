-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja30_original_negative_borel_partition_count_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:12:23.176879+00:00
-- url     : https://prove2.me/submissions/b04fc22b-a3dd-44f6-8a94-0f655cc82dde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja32_original_negative_borel_cell_exact_variance_20261111
import Theorems.Thm_AvramDividend_Classical_avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Split physical finite Borel partition moments into diagonal and disjoint-cell atoms. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hNeg : ∀ i ∈ F, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
    (∀ i ∈ F, Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i) ∧
    (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0) := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let r : ι → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let Y : ι → Ω → ℝ := fun i ω =>
    (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
  change (∀ i ∈ F, Integrable (fun ω => (Y i ω) ^ 2) P ∧
    (∫ ω, (Y i ω) ^ 2 ∂P) = r i) ∧
    (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0)
  constructor
  · intro i hi
    have h := avram_ja32_original_negative_borel_cell_exact_variance_20261111
      X hFinite T (B i) (hB i hi) (hNeg i hi)
    change Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i at h
    exact h
  · intro i hi j hj hij
    have h := avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
      X hFinite T (B i) (B j)
      (hB i hi) (hB j hj) (hNeg i hi) (hNeg j hj)
      (hDisj i hi j hj hij)
    change Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0 at h
    exact h
