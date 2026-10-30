-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_actual_stieltjes_eq_killed_record_grid_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:58:49.684828+00:00
-- url     : https://prove2.me/submissions/e67da0f3-b8d3-4ca2-95e5-9761d8b72581

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_all_killed_record_grid_prefixes_le_actual_stieltjes
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_stieltjes_le_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The original stopped Stieltjes dividend payout equals the increasing
supremum of finite discounted increments of its actual running-supremum regulator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) =
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (runningSup X (grid (k + 1)).toNNReal ω -
                runningSup X (grid k).toNNReal ω)
        else 0) := by
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
             ENNReal.ofReal (runningSup X (grid (k + 1)).toNNReal ω -
               runningSup X (grid k).toNNReal ω)
         else 0) =
      (let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
       ∑ k ∈ Finset.range N,
         (if ENNReal.ofReal (u (k + 1)) < τ then
           ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
         ENNReal.ofReal (runningSup X (u (k + 1)).toNNReal ω -
           runningSup X (u k).toNNReal ω)) := by
    simp only [hgrid, ite_mul, zero_mul]
  apply le_antisymm
  · rw [avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
      (dividendMeasure (runningSup X) ω) q τ]
    calc
      _ ≤ ⨆ n : ℕ, ⨆ N : ℕ,
            (let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
             ∑ k ∈ Finset.range N,
               (if ENNReal.ofReal (u (k + 1)) < τ then
                 ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
               ENNReal.ofReal (runningSup X (u (k + 1)).toNNReal ω -
                 runningSup X (u k).toNNReal ω)) :=
        avram_root29_05_actual_stieltjes_le_killed_record_grid_sup X ω q τ
      _ = _ := by
        apply iSup_congr
        intro n
        apply iSup_congr
        intro N
        exact (hsum n N).symm
  · exact avram_root29_05_all_killed_record_grid_prefixes_le_actual_stieltjes
      X ω τ q hq
