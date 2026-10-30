-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_stieltjes_eq_killed_record_grid_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:02:22.713729+00:00
-- url     : https://prove2.me/submissions/a5c10232-5018-4eef-aea9-be74493306b1

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_all_shifted_killed_record_grid_prefixes_le_actual_stieltjes
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stieltjes_le_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Full pathwise equality between the *actual* shifted future killed
Stieltjes dividend measure and all finite sampled future-record cash meshes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) =
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (M (grid (k + 1)).toNNReal - M (grid k).toNNReal)
        else 0) := by
  let M : ℝ≥0 → ℝ := fun v =>
    sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
  let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
  have hgrid (n j : ℕ) :
      (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ) =
      (j : ℝ) / ((n : ℝ) + 1) := by
    simp [NNReal.coe_mul, NNReal.coe_inv, Nat.cast_add, div_eq_mul_inv]
  have hsum (n N : ℕ) :
      (let grid : ℕ → ℝ := fun j =>
          (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
       ∑ k ∈ Finset.range N,
         if ENNReal.ofReal (grid (k + 1)) < τ then
           ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
             ENNReal.ofReal (M (grid (k + 1)).toNNReal -
               M (grid k).toNNReal)
         else 0) =
      (let grid : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
       ∑ k ∈ Finset.range N,
         (if ENNReal.ofReal (grid (k + 1)) < τ then
           ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) else 0) *
         ENNReal.ofReal (M (grid (k + 1)).toNNReal -
           M (grid k).toNNReal)) := by
    simp only [hgrid, ite_mul, zero_mul]
  apply le_antisymm
  · rw [avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
      μ q τ]
    calc
      _ ≤ ⨆ n : ℕ, ⨆ N : ℕ,
            (let grid : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
             ∑ k ∈ Finset.range N,
               (if ENNReal.ofReal (grid (k + 1)) < τ then
                 ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) else 0) *
               ENNReal.ofReal (M (grid (k + 1)).toNNReal -
                 M (grid k).toNNReal)) :=
        avram_root29_05_shifted_stieltjes_le_killed_record_grid_sup
          X ω age q τ
      _ = _ := by
        apply iSup_congr
        intro n
        apply iSup_congr
        intro N
        exact (hsum n N).symm
  · exact avram_root29_05_all_shifted_killed_record_grid_prefixes_le_actual_stieltjes
      X ω age τ q hq
