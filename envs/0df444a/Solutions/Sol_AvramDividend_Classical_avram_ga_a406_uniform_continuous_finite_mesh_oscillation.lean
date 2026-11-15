-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a406_uniform_continuous_finite_mesh_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:22:09.509609+00:00
-- url     : https://prove2.me/submissions/bb8ff191-5ec6-4233-8afa-3e7f051d45ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a55_uniform_continuous_mesh_oscillation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : UniformContinuousOn f (Icc 0 T))
    (s t : ℕ → ℕ → ℝ≥0)
    (hRange : ∀ m i : ℕ, i < m →
      s m i ∈ Icc 0 T ∧ t m i ∈ Icc 0 T)
    (hGap : ∀ m i : ℕ, i < m →
      dist (s m i) (t m i) ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          dist (f (s m i)) (f (t m i)) < ε := by
  classical
  let s' : ℕ → ℕ → ℝ≥0 := fun m i => if i < m then s m i else 0
  let t' : ℕ → ℕ → ℝ≥0 := fun m i => if i < m then t m i else 0
  have hr (m i : ℕ) : s' m i ∈ Icc 0 T ∧ t' m i ∈ Icc 0 T := by
    by_cases hi : i < m
    · simpa [s', t', hi] using hRange m i hi
    · simp [s', t', hi]
  have hg (m i : ℕ) :
      dist (s' m i) (t' m i) ≤ T / ((m : ℝ≥0) + 1) := by
    by_cases hi : i < m
    · simpa [s', t', hi] using hGap m i hi
    · simp only [s', t', hi, ite_false, dist_self]
      exact (T / ((m : ℝ≥0) + 1)).property
  intro ε hε
  obtain ⟨k, hk⟩ :=
    avram_ga_a55_uniform_continuous_mesh_oscillation
      f T hf s' t' hr hg ε hε
  refine ⟨k, ?_⟩
  intro m hm i hi
  simpa [s', t', hi] using hk m hm i
