-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:41:08.108627+00:00
-- url     : https://prove2.me/submissions/e584fe9e-f584-4d88-a380-ec31badd4e4f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a237_original_physical_mesh_uniform_deterministic_drift_square_energy_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a238_integrable_raw_energy_uniform_expected_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option maxHeartbeats 800000
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
    (∀ m, Integrable (F m) P) →
      ∀ m, (∫ ω, F m ω ∂P) ≤
        2 * ((n : ℝ) * X.σ^2 + ((n : ℝ) * X.c)^2) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro Δ s R Z F hFI
  let E : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω then (Z m i ω)^2 else 0
  have hPack := avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
    X hν n ρ hρstop
  have hEInt : ∀ m, Integrable (E m) P := by
    simpa only [E,Z,R,s,Δ] using hPack.2.1
  have hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ (n : ℝ)*X.σ^2 := by
    simpa only [E,Z,R,s,Δ] using hPack.2.2
  have hDrift (m : ℕ) : (m : ℝ) * ((Δ m : ℝ)*X.c)^2 ≤
      ((n : ℝ)*X.c)^2 :=
    avram_ga_a237_original_physical_mesh_uniform_deterministic_drift_square_energy_bound n m X.c
  have hPt (m : ℕ) (ω : Ω) :
      F m ω ≤ 2*E m ω+2*(m : ℝ)*((Δ m : ℝ)*X.c)^2 := by
    simpa only [F,E,R,Z,s,Δ,sub_add_cancel] using
      (avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
        X n m ρ ω)
  have hResult := avram_ga_a238_integrable_raw_energy_uniform_expected_transfer
    P F E (fun m => (m : ℝ)*((Δ m : ℝ)*X.c)^2)
    ((n : ℝ)*X.σ^2) (((n : ℝ)*X.c)^2)
    hFI hEInt hEB hDrift (by
      intro m ω
      simpa only [mul_assoc] using hPt m ω)
  simpa only [mul_add] using hResult
