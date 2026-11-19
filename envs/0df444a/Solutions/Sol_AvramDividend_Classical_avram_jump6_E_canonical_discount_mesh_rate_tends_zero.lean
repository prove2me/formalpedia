-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_canonical_discount_mesh_rate_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:23:37.723864+00:00
-- url     : https://prove2.me/submissions/57d9e916-86b6-4807-8e5a-5a3145bd7738

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (q V : ℝ) :
    Tendsto (fun j : ℕ => q * (1 / (((j : ℝ) + 1))) * V)
      atTop (𝓝 (0 : ℝ)) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa using (h.const_mul q).mul_const V
