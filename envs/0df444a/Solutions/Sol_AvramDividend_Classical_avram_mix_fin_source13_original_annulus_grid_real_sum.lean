-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin_source13_original_annulus_grid_real_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:06:35.978632+00:00
-- url     : https://prove2.me/submissions/5fdbd83c-e72d-4a6b-951d-b4e11e0ec3c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_offtime_product_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original finite-grid chronological annulus real-product expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (hstep : ∀ i, t i ≤ t (i + 1))
    (k : ℕ) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let r : ℕ → ℝ := fun i => ((t i : ℝ≥0∞) * X.ν B).toReal
    let q : ℕ → ℝ := fun i =>
      ((((t (i + 1) - t i : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal
    Integrable (fun ω =>
      ∑ i ∈ Finset.range k,
        (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) P ∧
    (∫ ω, (∑ i ∈ Finset.range k,
      (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) ∂P) =
      ∑ i ∈ Finset.range k, r i * q i := by
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  let r : ℕ → ℝ := fun i => ((t i : ℝ≥0∞) * X.ν B).toReal
  let q : ℕ → ℝ := fun i =>
    ((((t (i + 1) - t i : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal
  change Integrable (fun ω =>
      ∑ i ∈ Finset.range k,
        (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) P ∧
    (∫ ω, (∑ i ∈ Finset.range k,
      (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) ∂P) =
      ∑ i ∈ Finset.range k, r i * q i
  have hCell (i : ℕ) :
      Integrable (fun ω =>
        (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) P ∧
      (∫ ω, (J 0 (t i) ω).toReal *
        (J (t i) (t (i + 1)) ω).toReal ∂P) = r i * q i := by
    have h := avram_mix_fin_source13_original_annulus_offtime_product_mean
      X (t i) (t (i + 1)) (hstep i) n m hnm
    change Integrable (fun ω =>
        (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) P ∧
      (∫ ω, (J 0 (t i) ω).toReal *
        (J (t i) (t (i + 1)) ω).toReal ∂P) = r i * q i at h
    exact h
  have hInt : ∀ i ∈ Finset.range k,
      Integrable (fun ω =>
        (J 0 (t i) ω).toReal * (J (t i) (t (i + 1)) ω).toReal) P := by
    intro i hi
    exact (hCell i).1
  constructor
  · exact integrable_finset_sum (Finset.range k) hInt
  · rw [integral_finset_sum (Finset.range k) hInt]
    exact Finset.sum_congr rfl (fun i hi => (hCell i).2)