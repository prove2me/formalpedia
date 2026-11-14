-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a66_true_stopped_gaussian_taylor_positive_L1_from_raw_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:20.353883+00:00
-- url     : https://prove2.me/submissions/1d959bbb-3641-4722-8b1b-26680b1769b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a58_true_stop_positive_taylor_expected_energy_split
import Theorems.Thm_AvramDividend_Classical_avram_ga_a59_positive_energy_uniform_bound_large_tail_to_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Direct positive stopped Taylor L1 convergence from genuine stop-masked raw Gaussian source energy bounds and compact C2 coefficient modulus. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : ℕ → ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (a z : ℕ → ℕ → Ω → ℝ)
    (δ : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hAInt : ∀ m, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        a m i ω * (z m i ω)^2 else 0) P)
    (hEInt : ∀ m, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        (z m i ω)^2 else 0) P)
    (hTInt : ∀ j m, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        (if δ j ≤ |z m i ω| then (z m i ω)^2 else 0) else 0) P)
    (hEbound : ∀ m, (∫ ω, (∑ i ∈ Finset.range m,
        if s m i < ρ ω then (z m i ω)^2 else 0) ∂P) ≤ K)
    (hCoeff : ∀ ε : ℝ, 0 < ε →
      ∃ (j : ℕ) (M : ℝ),
        0 ≤ M ∧
        (∀ m ω i, i ∈ Finset.range m → s m i < ρ ω → 0 ≤ a m i ω) ∧
        (∀ m ω i, i ∈ Finset.range m → s m i < ρ ω → a m i ω ≤ M) ∧
        (∀ m ω i, i ∈ Finset.range m → s m i < ρ ω →
          |z m i ω| < δ j → a m i ω ≤ ε))
    (hTtail : ∀ j, Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        if s m i < ρ ω then
          (if δ j ≤ |z m i ω| then (z m i ω)^2 else 0)
        else 0) ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m : ℕ => ∫ ω, (∑ i ∈ Finset.range m,
      if s m i < ρ ω then a m i ω * (z m i ω)^2
      else 0) ∂P) atTop (𝓝 (0 : ℝ)) := by
  let A : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m, if s m i < ρ ω then
      a m i ω * (z m i ω)^2 else 0
  let E : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m, if s m i < ρ ω then (z m i ω)^2 else 0
  let T : ℕ → ℕ → Ω → ℝ := fun j m ω =>
    ∑ i ∈ Finset.range m, if s m i < ρ ω then
      (if δ j ≤ |z m i ω| then (z m i ω)^2 else 0) else 0
  have hPos (m : ℕ) (ω : Ω) : 0 ≤ A m ω := by
    rcases hCoeff 1 (by norm_num) with ⟨j,M,hM,ha,_,_⟩
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : s m i < ρ ω
    · simp only [if_pos h]
      exact mul_nonneg (ha m ω i hi h) (sq_nonneg _)
    · simp only [if_neg h, le_refl]
  have hModulus : ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
        ∀ m, (∫ ω, A m ω ∂P) ≤ η * (∫ ω, E m ω ∂P) +
            M * (∫ ω, T j m ω ∂P) := by
    intro η hη
    rcases hCoeff η hη with ⟨j,M,hM,ha,hBound,hSmall⟩
    refine ⟨j,M,hM,?_⟩
    intro m
    have h :=
      avram_ga_a58_true_stop_positive_taylor_expected_energy_split
        P (Finset.range m) (s m) ρ (a m) (z m) η M (δ j)
        hη.le
        (fun ω i hi hs => ha m ω i hi hs)
        (fun ω i hi hs => hBound m ω i hi hs)
        (fun ω i hi hs hd => hSmall m ω i hi hs hd)
    simpa only [A,E,T] using h (hAInt m) (hEInt m) (hTInt j m)
  exact avram_ga_a59_positive_energy_uniform_bound_large_tail_to_L1
    P A E T K hK
    (by intro m; exact hAInt m)
    hPos
    (by intro m; exact hEbound m)
    hModulus
    (by intro j; exact hTtail j)
