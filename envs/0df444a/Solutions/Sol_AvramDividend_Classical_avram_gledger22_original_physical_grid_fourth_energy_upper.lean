-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger22_original_physical_grid_fourth_energy_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:06:02.213448+00:00
-- url     : https://prove2.me/submissions/0920c4f3-4b37-47fc-904f-fe641b5c8d67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Sum the original Gaussian fourth interval moments on a deterministic grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ)) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2) := by
  classical
  let Z : ℕ → Ω → ℝ := fun i ω =>
    (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
  have hTimeMeas : Measurable (fun ω : Ω =>
      (X.X Δ ω - (Δ : ℝ) * X.c) / X.σ) := by
    have hX : Measurable (X.X Δ) :=
      (X.adapted Δ).mono (𝓕.le Δ) le_rfl
    fun_prop
  have hMom : ∀ i ∈ S,
      (∫⁻ ω, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
        ENNReal.ofReal (3 * (Δ : ℝ) ^ 2) := by
    intro i hi
    have hsi : s i ≤ s i + Δ :=
      le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ Δ)
    have hsource :=
      avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
        X hν hσ (s i) (s i + Δ) hsi
          (by simpa only [add_tsub_cancel_left] using hTimeMeas)
    simpa only [Z, add_tsub_cancel_left] using hsource
  have hf : ∀ i ∈ S,
      Measurable (fun ω => ENNReal.ofReal ((Z i ω) ^ 4)) := by
    intro i hi
    exact ENNReal.measurable_ofReal.comp ((hMeas i hi).pow_const 4)
  change (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
    ∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)
  rw [lintegral_finset_sum S hf]
  exact Finset.sum_le_sum hMom
