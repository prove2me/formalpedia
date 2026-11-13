-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a31_original_physical_grid_lindeberg_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:08:53.372834+00:00
-- url     : https://prove2.me/submissions/726ff533-bb34-484a-9d5f-577d447c7671

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_lindeberg_scalar_fourth_energy
import Theorems.Thm_AvramDividend_Classical_avram_gledger22_original_physical_grid_fourth_energy_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original Gaussian grid has a quantitative expected large-increment tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ S,
      ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) := by
  dsimp
  let Z : ℕ → Ω → ℝ := fun i ω =>
    (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
  change (∫⁻ ω, ∑ i ∈ S,
      ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2))
  have hFourthMeas :
      Measurable (fun ω : Ω =>
        ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4)) := by
    apply Finset.measurable_sum
    intro i hi
    have hZi : Measurable (Z i) := hMeas i hi
    fun_prop
  have hFactor (i : ℕ) (ω : Ω) :
      ENNReal.ofReal ((Z i ω) ^ 4 / r ^ 2) =
        ENNReal.ofReal (1 / r ^ 2) *
          ENNReal.ofReal ((Z i ω) ^ 4) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 : ℝ) / r ^ 2)]
    congr 1
    ring
  have hPoint (ω : Ω) :
      (∑ i ∈ S, ENNReal.ofReal
        (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        (∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4)) := by
    calc
      (∑ i ∈ S, ENNReal.ofReal
        (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)) ≤
        ∑ i ∈ S, ENNReal.ofReal (1 / r ^ 2) *
          ENNReal.ofReal ((Z i ω) ^ 4) := by
            apply Finset.sum_le_sum
            intro i hi
            calc
              ENNReal.ofReal
                (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ≤
                ENNReal.ofReal ((Z i ω) ^ 4 / r ^ 2) :=
                  ENNReal.ofReal_le_ofReal
                    (avram_ga_a27_lindeberg_scalar_fourth_energy r (Z i ω) hr)
              _ = ENNReal.ofReal (1 / r ^ 2) *
                  ENNReal.ofReal ((Z i ω) ^ 4) := hFactor i ω
      _ = ENNReal.ofReal (1 / r ^ 2) *
          (∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4)) := by
            rw [Finset.mul_sum]
  have hSource :
      (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2) := by
    exact avram_gledger22_original_physical_grid_fourth_energy_upper
      X hν hσ S s Δ hMeas
  calc
    (∫⁻ ω, ∑ i ∈ S,
      ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal (1 / r ^ 2) *
        (∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4)) ∂P :=
          lintegral_mono hPoint
    _ = ENNReal.ofReal (1 / r ^ 2) *
          (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) :=
            lintegral_const_mul _ hFourthMeas
    _ ≤ ENNReal.ofReal (1 / r ^ 2) *
          (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) := by
            gcongr <;> exact hSource
