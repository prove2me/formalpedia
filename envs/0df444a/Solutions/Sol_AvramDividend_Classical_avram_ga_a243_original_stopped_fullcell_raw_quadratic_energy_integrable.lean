-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:36:30.292707+00:00
-- url     : https://prove2.me/submissions/f47042c0-84ea-488e-a2a6-0a56004ba40e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a241_integrability_of_source_nonnegative_quadratic_energy_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a242_original_true_stopped_fullcell_raw_Gaussian_quadratic_energy_measurable
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
    ∀ m, Integrable (F m) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro Δ s R F
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    R m i ω-(Δ m : ℝ)*X.c
  let E : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω then (Z m i ω)^2 else 0
  have hPack := avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
    X hν n ρ hρstop
  have hEI : ∀ m, Integrable (E m) P := by
    simpa only [E,Z,R,s,Δ] using hPack.2.1
  have hFm (m : ℕ) : AEStronglyMeasurable (F m) P := by
    have hm := avram_ga_a242_original_true_stopped_fullcell_raw_Gaussian_quadratic_energy_measurable
      X n ρ hρstop m
    exact (show Measurable (F m) by
      simpa only [F,R,s,Δ] using hm).aestronglyMeasurable
  have hFpos (m : ℕ) (ω : Ω) : 0 ≤ F m ω := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hEpos (m : ℕ) (ω : Ω) : 0 ≤ E m ω := by
    dsimp [E]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hDrift (m : ℕ) :
      0 ≤ (m : ℝ)*((Δ m : ℝ)*X.c)^2 := by positivity
  have hPt (m : ℕ) (ω : Ω) :
      F m ω ≤ 2*E m ω +
        2*(m : ℝ)*((Δ m : ℝ)*X.c)^2 := by
    simpa only [F,E,R,Z,s,Δ,sub_add_cancel] using
      (avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
        X n m ρ ω)
  exact avram_ga_a241_integrability_of_source_nonnegative_quadratic_energy_majorant
    P F E (fun m => (m : ℝ)*((Δ m : ℝ)*X.c)^2)
    hDrift hFm hEI hFpos hEpos (by
      intro m ω
      simpa only [mul_assoc] using hPt m ω)
