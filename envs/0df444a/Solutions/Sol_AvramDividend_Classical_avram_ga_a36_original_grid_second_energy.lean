-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a36_original_grid_second_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:17:03.063971+00:00
-- url     : https://prove2.me/submissions/874b12a7-8e6d-4edd-93e1-34586651070c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

-- Genuine original centred Gaussian source increments have expected finite-grid quadratic energy.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c)) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 2) ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2) := by
  classical
  dsimp
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  change (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 2) ∂P) ≤
    ∑ _i ∈ S, ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2)
  have hMom (i : ℕ) (hi : i ∈ S) :
      (∫⁻ ω, ENNReal.ofReal ((Z i ω) ^ 2) ∂P) ≤
      ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2) := by
    have hStop : IsStoppingTime 𝓕.rightCont
        (fun _ : Ω => ((s i : ℝ≥0) : WithTop ℝ≥0)) :=
      isStoppingTime_const 𝓕.rightCont (s i)
    have hBound : ∀ ω : Ω, (s i) ≤ s i := by intro ω; exact le_refl _
    simpa only [Z] using
      (avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
        X hν (fun _ : Ω => s i) hStop (s i) hBound Δ)
  have hf : ∀ i ∈ S,
      Measurable (fun ω : Ω => ENNReal.ofReal ((Z i ω) ^ 2)) := by
    intro i hi
    exact ENNReal.measurable_ofReal.comp ((hMeas i hi).pow_const 2)
  rw [lintegral_finset_sum S hf]
  exact Finset.sum_le_sum hMom
