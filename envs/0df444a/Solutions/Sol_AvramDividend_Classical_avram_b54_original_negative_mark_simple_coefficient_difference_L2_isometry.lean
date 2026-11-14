-- Prove2me | solution 1 for AvramDividend.Classical.avram_b54_original_negative_mark_simple_coefficient_difference_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:24.307593+00:00
-- url     : https://prove2.me/submissions/27b44a42-24b3-4ddf-b383-1aa203270fba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original physical compensated negative mark simple-integrand L2 difference isometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ) (B : ℕ → Set ℝ)
    (a b : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range K, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
      i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((t : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 t ×ˢ B i)).toReal - r i
    let A : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K, a i * Y i ω
    let C : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K, b i * Y i ω
    Integrable (fun ω => (A ω - C ω)^2) P ∧
    (∫ ω, (A ω - C ω)^2 ∂P) =
      ∑ i ∈ Finset.range K, (a i - b i)^2 * r i := by 
  classical
  dsimp only
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let r : ℕ → ℝ := fun i => ((t : ℝ≥0∞) * X.ν (B i)).toReal
  let Y : ℕ → Ω → ℝ := fun i ω =>
    (NX ω (Ioc 0 t ×ˢ B i)).toReal - r i
  have h := avram_ja31_original_finite_borel_mark_source_isometry
    X hFinite t (Finset.range K) B (fun i => a i - b i)
    hB hNeg hDisj
  dsimp only at h
  have hF (ω : Ω) :
      (∑ i ∈ Finset.range K, a i * Y i ω) -
        (∑ i ∈ Finset.range K, b i * Y i ω) =
      ∑ i ∈ Finset.range K, (a i - b i) * Y i ω := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change
    Integrable (fun ω =>
      ((∑ i ∈ Finset.range K, a i * Y i ω) -
        (∑ i ∈ Finset.range K, b i * Y i ω)) ^ 2) P ∧
    (∫ ω, ((∑ i ∈ Finset.range K, a i * Y i ω) -
      (∑ i ∈ Finset.range K, b i * Y i ω)) ^ 2 ∂P) =
      ∑ i ∈ Finset.range K, (a i - b i)^2 * r i
  have hPow : (fun ω =>
      ((∑ i ∈ Finset.range K, a i * Y i ω) -
        (∑ i ∈ Finset.range K, b i * Y i ω)) ^ 2) =
      (fun ω => (∑ i ∈ Finset.range K,
        (a i - b i) * Y i ω) ^ 2) := by
    funext ω
    rw [hF ω]
  rw [hPow]
  exact h
