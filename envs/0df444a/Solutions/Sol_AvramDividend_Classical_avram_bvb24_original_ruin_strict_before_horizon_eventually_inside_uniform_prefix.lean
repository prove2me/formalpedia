-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_ruin_strict_before_horizon_eventually_inside_uniform_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:03.254541+00:00
-- url     : https://prove2.me/submissions/87327de6-296a-4a97-a064-0df81ab149e4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (τ T : ℝ) (hτT : τ < T) :
    ∀ᶠ n : ℕ in atTop, τ < T - T / ((n : ℝ) + 2)  := by
  have hDiv : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hShift :=
      (Filter.tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => T / (n : ℝ))
        (l := 𝓝 (0 : ℝ)) 2).2
        (tendsto_const_div_atTop_nhds_zero_nat T)
    simpa [Nat.cast_add] using hShift
  have hPrefix : Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2))
      atTop (𝓝 T) := by
    simpa using (tendsto_const_nhds.sub hDiv)
  simpa only [Set.mem_Ioi] using
    hPrefix.eventually (isOpen_Ioi.mem_nhds hτT)
