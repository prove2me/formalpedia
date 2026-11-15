-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finite_mark_step_path_exact_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:21:12.576229+00:00
-- url     : https://prove2.me/submissions/77e65738-7075-46a4-84f7-69a8095d6e3b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a30_single_mark_causal_step_left_limit_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun v : ℝ≥0 =>
      ∑ u ∈ S, if u ≤ v then z u else 0)
      (𝓝[<] t) (𝓝 (∑ u ∈ S, if u < t then z u else 0))  := by
  apply tendsto_finset_sum S
  intro u hu
  exact avram_a30_single_mark_causal_step_left_limit_20261114 u (z u) t ht
