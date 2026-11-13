-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a55_uniform_continuous_mesh_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:05:01.630176+00:00
-- url     : https://prove2.me/submissions/aa92bb26-9bf3-48d1-af99-8ddd14eddd21

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Metric
open scoped NNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : UniformContinuousOn f (Icc 0 T))
    (s t : ℕ → ℕ → ℝ≥0)
    (hRange : ∀ m i : ℕ, s m i ∈ Icc 0 T ∧ t m i ∈ Icc 0 T)
    (hGap : ∀ m i : ℕ,
      dist (s m i) (t m i) ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      ∀ i : ℕ, dist (f (s m i)) (f (t m i)) < ε := by
  intro ε hε
  obtain ⟨ δ, hδ, hmod ⟩ :=
    (Metric.uniformContinuousOn_iff.mp hf) ε hε
  obtain ⟨ k, hk ⟩ := exists_nat_gt ((T : ℝ) / δ)
  refine ⟨ k, ?_ ⟩
  intro m hm i
  have hmReal : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq : (T : ℝ) / δ < (m : ℝ) + 1 := by linarith
  have hmul : (T : ℝ) < δ * ((m : ℝ) + 1) := by
    have h := (div_lt_iff₀ hδ).mp hq
    nlinarith
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hwidth :
      ((T / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) < δ := by
    rw [NNReal.coe_div]
    push_cast
    exact (div_lt_iff₀ hden).mpr (by nlinarith)
  exact hmod (s m i) (hRange m i).1 (t m i) (hRange m i).2
    (lt_of_le_of_lt (hGap m i) hwidth)
