-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a215_original_prefix_raw_centered_square_cross_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:34:55.977298+00:00
-- url     : https://prove2.me/submissions/b68a55ff-d491-44ae-86ac-98c8158718f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a81_original_stopped_gaussian_raw_centered_cross_energy_expected_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_ga_a86_original_gaussian_uniform_mesh_drift_square_mass_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Cross : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω then |R^2 - Z^2| else 0
    (∀ m : ℕ, Integrable (Cross m) P) ∧
    Tendsto (fun m : ℕ => ∫ ω, Cross m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  intro Cross
  letI : IsProbabilityMeasure P := X.isProbability
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let d : ℕ → ℝ := fun m => (Δ m : ℝ) * X.c
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω - d m
  let f : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    |(Z m i ω + d m)^2 - (Z m i ω)^2|
  let A : ℕ → ℕ → Ω → Prop := fun m i ω => s m i < ρ ω
  let Prefix : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m, if A m i ω then f m i ω else 0
  let Energy : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m, if A m i ω then (Z m i ω)^2 else 0
  have hPack := avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
    X hNuZero n ρ hρstop
  change (∀ m, Integrable (Prefix m) P) ∧
    (∀ m, Integrable (Energy m) P) ∧
    (∀ m, (∫ ω, Energy m ω ∂P) ≤ (n : ℝ) * X.σ^2) at hPack
  obtain ⟨hAI,hEI,hEBound⟩ := hPack
  have hPrefix : Tendsto (fun m => ∫ ω, Prefix m ω ∂P) atTop (𝓝 (0 : ℝ)) :=
    avram_ga_a81_original_stopped_gaussian_raw_centered_cross_energy_expected_L1_vanish
      P s ρ Z d ((n : ℝ) * X.σ^2) (by positivity)
      hAI hEI hEBound
      (avram_ga_a86_original_gaussian_uniform_mesh_drift_square_mass_vanish n X.c)
  have hEq (m : ℕ) (ω : Ω) : Cross m ω = Prefix m ω := by
    dsimp [Cross,Prefix,A,f,Z,d,s,Δ]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> try rfl
    congr 1
    ring
  refine ⟨(fun m => (hAI m).congr
    (Filter.Eventually.of_forall (fun ω => (hEq m ω).symm))),?_⟩
  convert hPrefix using 1
  funext m
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => hEq m ω))
