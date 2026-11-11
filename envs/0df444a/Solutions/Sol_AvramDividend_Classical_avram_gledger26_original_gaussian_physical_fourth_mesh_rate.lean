-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger26_original_gaussian_physical_fourth_mesh_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:14:16.77855+00:00
-- url     : https://prove2.me/submissions/098c9fff-ffb0-42aa-a467-1bb842dbfc0d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger22_original_physical_grid_fourth_energy_upper
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian finite-mesh fourth energy has the explicit
    order-one-over-m bound needed for the large-source Taylor tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n m : ℕ)
    (hMeas : ∀ i ∈ Finset.range m,
      Measurable (fun ω : Ω =>
        (X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          (((n : ℝ≥0) / ((m : ℝ≥0) + 1)) : ℝ) * X.c) / X.σ)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X ((i : ℝ≥0) * Δ + Δ) ω -
        X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
      ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Z : ℕ → Ω → ℝ := fun i ω =>
    (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
  change (∫⁻ ω, ∑ i ∈ Finset.range m,
    ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
      ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1))
  have hBound := avram_gledger22_original_physical_grid_fourth_energy_upper
    X hν hσ (Finset.range m) s Δ (by
      intro i hi
      simpa only [s, Δ, NNReal.coe_div, NNReal.coe_add,
        NNReal.coe_natCast, NNReal.coe_one] using hMeas i hi)
  have hB :
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
        ∑ _i ∈ Finset.range m, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2) := by
    simpa only [Z] using hBound
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have ht0 : 0 ≤ 3 * (Δ : ℝ) ^ 2 := by positivity
  have hSum :
      (∑ _i ∈ Finset.range m, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) =
        ENNReal.ofReal ((m : ℝ) * (3 * (Δ : ℝ) ^ 2)) := by
    simp [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul, ht0]
  have hDelta : (Δ : ℝ) = (n : ℝ) / ((m : ℝ) + 1) := by
    simp only [Δ, NNReal.coe_div, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_one]
  have hMul :
      (m : ℝ) * (3 * (n : ℝ) ^ 2) ≤
        ((m : ℝ) + 1) * (3 * (n : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_right
    · linarith
    · positivity
  have hReal :
      (m : ℝ) * (3 * (Δ : ℝ) ^ 2) ≤
        3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1) := by
    rw [hDelta]
    field_simp
    nlinarith [hMul]
  calc
    _ ≤ (∑ _i ∈ Finset.range m,
          ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) := hB
    _ = ENNReal.ofReal ((m : ℝ) * (3 * (Δ : ℝ) ^ 2)) := hSum
    _ ≤ ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) :=
      ENNReal.ofReal_le_ofReal hReal
