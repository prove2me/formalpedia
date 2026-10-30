-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_killed_record_rational_reward_indicator_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:24:15.294441+00:00
-- url     : https://prove2.me/submissions/b23d8a42-d978-4013-857a-415fd0f5efc2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Source killed-record future rational reward, even with its nested
stopped-prefix indicator, is exactly the measurable record event mass. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Ω × ℝ)) (τ : Ω → ℝ≥0) (A : Set Ω)
    (Y : Ω → (ℝ≥0 → ℝ)) (a : ℝ) :
    (let B : Set (Ω × ℝ) := {z | (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
           0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)}
     let H : Ω × ℝ → ℝ≥0∞ := fun z =>
       if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
           0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
       then 1 else 0
     (∫⁻ z, if (τ z.1 : ℝ) ≤ z.2 then
        (if z.1 ∈ A then (1 : ℝ≥0∞) else 0) * H z else 0 ∂μ) =
     (∫⁻ z, B.indicator (fun _ => (1 : ℝ≥0∞)) z ∂μ)) := by
  classical
  intro B H
  apply lintegral_congr
  intro z
  by_cases ht : (τ z.1 : ℝ) ≤ z.2
  · by_cases hA : z.1 ∈ A
    · by_cases hGrid : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
          0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)
      · simp [B, H, Set.indicator, ht, hA, hGrid]
      · simp [B, H, Set.indicator, ht, hA, hGrid]
    · simp [B, H, Set.indicator, ht, hA]
  · simp [B, H, Set.indicator, ht]
