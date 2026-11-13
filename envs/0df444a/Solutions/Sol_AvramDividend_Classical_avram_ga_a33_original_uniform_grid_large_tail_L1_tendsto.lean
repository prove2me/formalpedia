-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a33_original_uniform_grid_large_tail_L1_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:07:54.072076+00:00
-- url     : https://prove2.me/submissions/1fbda73b-2c1e-44a6-ba1f-d1d5f68164d0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a31_original_physical_grid_lindeberg_energy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a32_lindeberg_uniform_mesh_real_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

-- Original physical Gaussian mesh large-increment quadratic energy vanishes in L1.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω =>
        (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
          X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ
    Tendsto (fun m : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range m,
        ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  dsimp
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    (X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c) / X.σ
  change Tendsto (fun m : ℕ =>
    ∫⁻ ω, ∑ i ∈ Finset.range m,
      ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P)
    atTop (𝓝 (0 : ℝ≥0∞))
  have hBound (m : ℕ) :
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P) ≤
        ENNReal.ofReal (1 / r ^ 2) *
          ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) := by
    have hGrid :
        (∫⁻ ω, ∑ i ∈ Finset.range m,
          ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P) ≤
          ENNReal.ofReal (1 / r ^ 2) *
            (∑ _i ∈ Finset.range m,
              ENNReal.ofReal (3 * (Δ m : ℝ) ^ 2)) := by
      exact avram_ga_a31_original_physical_grid_lindeberg_energy
        X hν hσ (Finset.range m)
        (fun i => (i : ℝ≥0) * Δ m) (Δ m) (hMeas m) r hr
    have hWidth :
        (∑ _i ∈ Finset.range m,
          ENNReal.ofReal (3 * (Δ m : ℝ) ^ 2)) =
        (∑ _i ∈ Finset.range m,
          ENNReal.ofReal (3 * ((n : ℝ) / ((m : ℝ) + 1)) ^ 2)) := by
      simp only [hΔ m]
    have hLift :
        (∑ _i ∈ Finset.range m,
          ENNReal.ofReal (3 * ((n : ℝ) / ((m : ℝ) + 1)) ^ 2)) =
        ENNReal.ofReal
          (∑ _i ∈ Finset.range m,
            (3 : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) ^ 2) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg
        (fun _i _hi => by positivity)
    calc
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        ENNReal.ofReal (if r ≤ |Z m i ω| then (Z m i ω) ^ 2 else 0) ∂P) ≤
          ENNReal.ofReal (1 / r ^ 2) *
            (∑ _i ∈ Finset.range m,
              ENNReal.ofReal (3 * (Δ m : ℝ) ^ 2)) := hGrid
      _ = ENNReal.ofReal (1 / r ^ 2) *
            ENNReal.ofReal
              (∑ _i ∈ Finset.range m,
                (3 : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) ^ 2) := by
          rw [hWidth, hLift]
      _ ≤ ENNReal.ofReal (1 / r ^ 2) *
            ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) := by
          gcongr
          exact avram_ga_a32_lindeberg_uniform_mesh_real_rate n m
  have hRate : Tendsto (fun m : ℕ => 3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heq : (fun m : ℕ => 3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) =
        (fun m : ℕ => (3 * (n : ℝ) ^ 2) *
          ((1 : ℝ) / ((m : ℝ) + 1))) := by
      funext m
      ring
    rw [heq]
    simpa using ht.const_mul (3 * (n : ℝ) ^ 2)
  have hENN : Tendsto (fun m : ℕ => ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hRate
  have hConst : ENNReal.ofReal (1 / r ^ 2) ≠ ⊤ := by simp
  have hUpper : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / r ^ 2) *
      ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1))) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using (ENNReal.Tendsto.const_mul hENN (Or.inr hConst))
  apply Filter.Tendsto.squeeze
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hUpper
  · intro m; exact zero_le
  · intro m; exact hBound m
