-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_centered_quadratic_uniform_mesh_second_moment_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:21:51.37201+00:00
-- url     : https://prove2.me/submissions/c7fb27e7-1911-4ea9-be07-8a7820dfbf1d

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_ga_predictable_centered_quadratic_mesh_L2_diagonal_bound
open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : ℕ → Filtration ℕ mΩ)
    (H : ℕ → ℕ → Ω → ℝ)
    (hLp : ∀ m i, MemLp (H m i) 2 P)
    (hAdapt : ∀ m i, StronglyMeasurable[(𝓕 m) (i + 1)] (H m i))
    (hCenter : ∀ m i, P[H m i | (𝓕 m) i] =ᵐ[P] 0)
    (K T : ℝ)
    (hVar : ∀ m i, i < m + 1 →
      (∫ ω, (H m i ω) ^ 2 ∂P) ≤
        K * (T / ((m : ℝ) + 1)) ^ 2) :
    ∀ m : ℕ,
      (∫ ω, (∑ i ∈ Finset.range (m + 1), H m i ω) ^ 2 ∂P) ≤
        K * T ^ 2 / ((m : ℝ) + 1) := by
  intro m
  have hb := avram_ga_predictable_centered_quadratic_mesh_L2_diagonal_bound
    P (𝓕 m) (H m) (hLp m) (hAdapt m) (hCenter m)
    (m + 1) K (T / ((m : ℝ) + 1)) (hVar m)
  calc
    (∫ ω, (∑ i ∈ Finset.range (m + 1), H m i ω) ^ 2 ∂P) ≤
        ((m + 1 : ℕ) : ℝ) *
          (K * (T / ((m : ℝ) + 1)) ^ 2) := hb
    _ = K * T ^ 2 / ((m : ℝ) + 1) := by
      have hden : (m : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
