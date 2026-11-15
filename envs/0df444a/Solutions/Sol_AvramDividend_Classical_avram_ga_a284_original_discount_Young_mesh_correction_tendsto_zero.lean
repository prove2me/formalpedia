-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a284_original_discount_Young_mesh_correction_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:36:12.713386+00:00
-- url     : https://prove2.me/submissions/75af3b15-2bff-438e-8bb0-fdc4d6cc235f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal Topology
noncomputable section
theorem solution (n : ℕ) (q L η : ℝ) (hη : 0 < η) :
    Tendsto (fun m : ℕ =>
      (m : ℝ)*(q*((((n : ℝ≥0) / ((m : ℝ≥0)+1)) : ℝ≥0) : ℝ)*L)^2/(4*η))
      atTop (𝓝 (0 : ℝ)) := by
  have hsmall : Tendsto (fun m : ℕ =>
      (m : ℝ)/((m : ℝ)+1)^2) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
    · filter_upwards with m
      positivity
    · filter_upwards with m
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
  have h := hsmall.const_mul ((q*(n : ℝ)*L)^2/(4*η))
  convert h using 1
  · funext m
    simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    field_simp <;> ring
  · simp
