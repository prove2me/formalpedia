-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_rational_age_fullPath_survival_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:08:51.872276+00:00
-- url     : https://prove2.me/submissions/dac9fd98-717e-4c4b-80b8-4c3943b8e41a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Measurable full-path survival test at a variable nonnegative age,
using only a countable family of fixed rational time coordinates. -/
theorem solution (a : ℝ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < z.1 →
          0 ≤ a + z.2 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
      then (1 : ℝ≥0∞) else 0) := by
  classical
  let g : ℕ → ℕ → ℝ≥0 := fun n k =>
    (k : ℝ≥0) * (n : ℝ≥0)⁻¹
  have hTest (n k : ℕ) : MeasurableSet
      {z : ℝ≥0 × (ℝ≥0 → ℝ) |
        g n k < z.1 → 0 ≤ a + z.2 (g n k)} := by
    have ht : MeasurableSet
        {z : ℝ≥0 × (ℝ≥0 → ℝ) | g n k < z.1} :=
      measurableSet_lt measurable_const measurable_fst
    have hx : MeasurableSet
        {z : ℝ≥0 × (ℝ≥0 → ℝ) | 0 ≤ a + z.2 (g n k)} :=
      measurableSet_le measurable_const
        (measurable_const.add
          ((measurable_pi_apply (g n k)).comp measurable_snd))
    have heq :
        {z : ℝ≥0 × (ℝ≥0 → ℝ) |
          g n k < z.1 → 0 ≤ a + z.2 (g n k)} =
        {z : ℝ≥0 × (ℝ≥0 → ℝ) | g n k < z.1}ᶜ ∪
        {z : ℝ≥0 × (ℝ≥0 → ℝ) | 0 ≤ a + z.2 (g n k)} := by
      ext z
      simp [imp_iff_not_or]
    rw [heq]
    exact ht.compl.union hx
  have hForall (n : ℕ) : MeasurableSet
      {z : ℝ≥0 × (ℝ≥0 → ℝ) |
        0 < n → ∀ k : ℕ, g n k < z.1 → 0 ≤ a + z.2 (g n k)} := by
    by_cases hn : 0 < n
    · have heq :
        {z : ℝ≥0 × (ℝ≥0 → ℝ) |
          0 < n → ∀ k : ℕ, g n k < z.1 →
            0 ≤ a + z.2 (g n k)} =
        ⋂ k : ℕ, {z : ℝ≥0 × (ℝ≥0 → ℝ) |
          g n k < z.1 → 0 ≤ a + z.2 (g n k)} := by
        ext z
        simp [hn]
      rw [heq]
      exact MeasurableSet.iInter (hTest n)
    · have heq :
        {z : ℝ≥0 × (ℝ≥0 → ℝ) |
          0 < n → ∀ k : ℕ, g n k < z.1 →
            0 ≤ a + z.2 (g n k)} = Set.univ := by
        ext z
        simp [hn]
      rw [heq]
      exact MeasurableSet.univ
  have hAll : MeasurableSet
      {z : ℝ≥0 × (ℝ≥0 → ℝ) |
        ∀ n : ℕ, 0 < n → ∀ k : ℕ,
          g n k < z.1 → 0 ≤ a + z.2 (g n k)} := by
    have heq :
      {z : ℝ≥0 × (ℝ≥0 → ℝ) |
        ∀ n : ℕ, 0 < n → ∀ k : ℕ,
          g n k < z.1 → 0 ≤ a + z.2 (g n k)} =
      ⋂ n : ℕ, {z : ℝ≥0 × (ℝ≥0 → ℝ) |
        0 < n → ∀ k : ℕ,
          g n k < z.1 → 0 ≤ a + z.2 (g n k)} := by
      ext z
      simp
    rw [heq]
    exact MeasurableSet.iInter hForall
  simpa only [g] using
    (measurable_const.ite hAll measurable_const)
