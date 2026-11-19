-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_discount_mesh_error_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:30:02.286215+00:00
-- url     : https://prove2.me/submissions/d4d8bc24-51da-4478-b5ff-094df8164d8b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

theorem solution
    (q V : ℝ) :
    Tendsto (fun j : ℕ => q * (1 / ((j : ℝ) + 1)) * V)
      atTop (𝓝 (0 : ℝ)) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa using (h.const_mul q).mul_const V
