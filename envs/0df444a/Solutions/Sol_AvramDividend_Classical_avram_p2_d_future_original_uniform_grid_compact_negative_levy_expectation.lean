-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_original_uniform_grid_compact_negative_levy_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:08:36.755492+00:00
-- url     : https://prove2.me/submissions/068f0b85-cee5-4d23-9089-00b51aa4b095

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_stationary_real_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-exact expected uniform-grid compact-negative jump tests converge to
the genuine triplet Lévy intensity. No intrinsic-jump compensator is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hInt : ∀ t : ℝ≥0, Integrable (fun ω => f (X.X t ω)) P)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ ω, ∑ i ∈ Finset.range (n + 1),
      f (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
         X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P)
      atTop (𝓝 ((T : ℝ) *
        (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))))) := by
  have hSource :=
    avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
      X f hf a ε hε hflower hfupper T hT
  have hSourceNN :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
        (∫ ω, f (X.X (T / ((n : ℝ≥0) + 1)) ω) ∂P))
        atTop (𝓝 ((T : ℝ) *
          (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))))) := by
    simpa only [avram_p2_a_zero_rate_real_nnreal_uniform_step_coe] using hSource
  have hCell (n : ℕ) :
      (∫ ω, ∑ i ∈ Finset.range (n + 1),
        f (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
           X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
      ((n : ℝ) + 1) *
        (∫ ω, f (X.X (T / ((n : ℝ≥0) + 1)) ω) ∂P) := by
    let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
    have hGrid (i : ℕ) (_ : i < n + 1) : grid i ≤ grid (i + 1) := by
      dsimp [grid]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_succ i
      · exact zero_le
    have hIntGrid (i : ℕ) (_ : i < n + 1) :
        Integrable (fun ω => f (X.X
          (((0 : ℝ≥0) + grid (i + 1)) - ((0 : ℝ≥0) + grid i)) ω)) P :=
      hInt _
    have hStationary :=
      avram_p2_j_ui_original_grid_stationary_real_integral
        X 0 (n + 1) grid hGrid f hf.measurable hIntGrid
    have hDuration (i : ℕ) :
        ((0 : ℝ≥0) + grid (i + 1)) -
            ((0 : ℝ≥0) + grid i) = δ := by
      simp only [zero_add]
      dsimp [grid]
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact add_tsub_cancel_left _ _
    calc
      _ = ∑ i ∈ Finset.range (n + 1),
          ∫ ω, f (X.X (((0 : ℝ≥0) + grid (i + 1)) -
            ((0 : ℝ≥0) + grid i)) ω) ∂P := by
              simpa [grid, δ] using hStationary
      _ = ∑ i ∈ Finset.range (n + 1),
          ∫ ω, f (X.X δ ω) ∂P := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hDuration i]
      _ = _ := by
          simp [δ, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
  simpa only [hCell] using hSourceNN
