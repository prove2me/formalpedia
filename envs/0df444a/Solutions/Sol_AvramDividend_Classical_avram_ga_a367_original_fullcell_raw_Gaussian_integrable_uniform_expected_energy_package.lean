-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a367_original_fullcell_raw_Gaussian_integrable_uniform_expected_energy_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:10:51.774754+00:00
-- url     : https://prove2.me/submissions/186ac857-f872-445c-98b1-4cda87774519

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let F : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
        then (R m i ω)^2 else 0
    let K : ℝ := 2 * ((n : ℝ) * X.σ^2 + ((n : ℝ) * X.c)^2)
    0 ≤ K ∧ (∀ m, Integrable (F m) P) ∧
      ∀ m, (∫ ω, F m ω ∂P) ≤ K := by
  intro Δ s R Z F K
  have hI := avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
    X hν n ρ hρstop
  have hB := avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
    X hν n ρ hρstop hI
  exact ⟨by dsimp [K]; positivity, hI, hB⟩
