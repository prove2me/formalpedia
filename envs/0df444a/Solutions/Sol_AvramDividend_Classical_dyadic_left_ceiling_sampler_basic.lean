-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_left_ceiling_sampler_basic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:08:46.542454+00:00
-- url     : https://prove2.me/submissions/6d28fee1-2c1b-4cf9-b45a-1252df9c6108

import Mathlib
open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

theorem solution (n : ℕ) :
    let g : ℝ≥0 → ℝ≥0 :=
      fun t : ℝ≥0 => ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n) - 1 / (2 : ℝ≥0) ^ n
    Measurable g ∧ (∀ t, g t ≤ t) ∧
      (∀ T, (g '' Iic T).Finite) := by
  intro g
  have hpos : (0:ℝ≥0) < 2 ^ n := pow_pos (by norm_num) n
  refine ⟨?_, ?_, ?_⟩
  · have : Measurable fun t : ℝ≥0 => Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) :=
      Nat.measurable_ceil.comp (measurable_coe_nnreal_real.mul_const _)
    exact ((measurable_from_nat.comp this).div_const _).sub_const _
  · intro t
    show ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n) - 1 / (2 : ℝ≥0) ^ n ≤ t
    rw [tsub_le_iff_right, div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne']
    rw [← NNReal.coe_le_coe]; push_cast
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (t:ℝ) * 2 ^ n by positivity)
    linarith
  · intro T
    have : g '' Iic T ⊆ (fun k : ℕ => ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) - 1 / (2 : ℝ≥0) ^ n) ''
        Iic (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n)) := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨_, ?_, rfl⟩
      exact Nat.ceil_mono (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 ht) (by positivity))
    exact ((finite_Iic _).image _).subset this
