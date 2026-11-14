-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a81_original_stopped_gaussian_raw_centered_cross_energy_expected_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:20:35.658483+00:00
-- url     : https://prove2.me/submissions/12b8707e-a8aa-4062-954f-848511c20037

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a80_original_stopped_gaussian_raw_centered_cross_energy_finite_mesh_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a59_positive_energy_uniform_bound_large_tail_to_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The genuine stopped Gaussian quadratic raw-centred cross error vanishes in expected absolute L1 whenever the source quadratic budget is bounded and total squared mesh drift vanishes. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (s : ℕ → ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (Z : ℕ → ℕ → Ω → ℝ) (d : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hAI : ∀ m : ℕ, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        |(Z m i ω + d m)^2 - (Z m i ω)^2| else 0) P)
    (hEI : ∀ m : ℕ, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        (Z m i ω)^2 else 0) P)
    (hEBound : ∀ m : ℕ,
      (∫ ω, (∑ i ∈ Finset.range m, if s m i < ρ ω then
        (Z m i ω)^2 else 0) ∂P) ≤ K)
    (hDriftMass : Tendsto (fun m : ℕ => (m : ℝ) * (d m)^2)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m : ℕ => ∫ ω, (∑ i ∈ Finset.range m,
      if s m i < ρ ω then
        |(Z m i ω + d m)^2 - (Z m i ω)^2|
      else 0) ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  let A : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m, if s m i < ρ ω then
      |(Z m i ω + d m)^2 - (Z m i ω)^2| else 0
  let E : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m, if s m i < ρ ω then
      (Z m i ω)^2 else 0
  let T : ℕ → ℕ → Ω → ℝ := fun _ m _ => (m : ℝ) * (d m)^2
  change Tendsto (fun m => ∫ ω, A m ω ∂P) atTop (𝓝 (0 : ℝ))
  have hPos (m : ℕ) (ω : Ω) : 0 ≤ A m ω := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : s m i < ρ ω
    · simpa only [if_pos h] using
        (abs_nonneg ((Z m i ω + d m)^2 - (Z m i ω)^2))
    · simp only [if_neg h, le_refl]
  have hModulus : ∀ ε : ℝ, 0 < ε →
      ∃ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
        ∀ m, (∫ ω, A m ω ∂P) ≤
          ε * (∫ ω, E m ω ∂P) +
            M * (∫ ω, T j m ω ∂P) := by
    intro ε hε
    have hM : 0 ≤ 1 + 1 / ε := by positivity
    refine ⟨0, 1 + 1 / ε, hM, ?_⟩
    intro m
    have hPoint (ω : Ω) : A m ω ≤
        ε * E m ω + (1 + 1 / ε) * ((m : ℝ) * (d m)^2) := by
      have h := avram_ga_a80_original_stopped_gaussian_raw_centered_cross_energy_finite_mesh_bound
        (Finset.range m) (s m) ρ ω (fun i => Z m i ω) (d m) ε hε
      calc
        A m ω ≤ ε * E m ω +
            (m : ℝ) * ((1 + 1 / ε) * (d m)^2) := by
          simpa only [A, E, Finset.card_range] using h
        _ = ε * E m ω + (1 + 1 / ε) * ((m : ℝ) * (d m)^2) := by ring
    have hTI : Integrable (fun ω : Ω => T 0 m ω) P := by
      change Integrable (fun _ : Ω => (m : ℝ) * (d m)^2) P
      exact integrable_const _
    have hPointT (ω : Ω) :
        A m ω ≤ ε * E m ω + (1 + 1 / ε) * T 0 m ω :=
      hPoint ω
    calc
      (∫ ω, A m ω ∂P) ≤
          (∫ ω, ε * E m ω + (1 + 1 / ε) * T 0 m ω ∂P) :=
        integral_mono (hAI m)
          (((hEI m).const_mul ε).add (hTI.const_mul _))
          hPointT
      _ = ε * (∫ ω, E m ω ∂P) +
          (1 + 1 / ε) * (∫ ω, T 0 m ω ∂P) := by
        rw [integral_add ((hEI m).const_mul ε) (hTI.const_mul _)]
        rw [integral_const_mul, integral_const_mul]
  have hTail (j : ℕ) : Tendsto
      (fun m : ℕ => ∫ ω, T j m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    have hEq : (fun m : ℕ => ∫ ω, T j m ω ∂P) =
        (fun m : ℕ => (m : ℝ) * (d m)^2) := by
      funext m
      simp [T, measure_univ]
    rw [hEq]
    exact hDriftMass
  exact avram_ga_a59_positive_energy_uniform_bound_large_tail_to_L1
    P A E T K hK
    (by intro m; exact hAI m)
    hPos
    (by intro m; exact hEBound m)
    hModulus hTail
