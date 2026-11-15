-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a244_original_gaussian_true_stopped_fullcell_raw_quadratic_uniform_expected_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:51:08.445609+00:00
-- url     : https://prove2.me/submissions/7d1a88cd-d7fc-4ff0-8eaf-56e5e489affc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    let F : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
        then (R m i ω)^2 else 0
    (∀ m, Integrable (F m) P) ∧
    (∀ m, (∫ ω, F m ω ∂P) ≤
      2 * ((n : ℝ) * X.σ^2 + ((n : ℝ) * X.c)^2)) := by
  intro Δ s R F
  have hInt := avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
    X hν n ρ hρstop
  have hBound := avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
    X hν n ρ hρstop hInt
  exact ⟨hInt,hBound⟩
