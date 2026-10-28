-- Prove2me | solution 1 for AvramDividend.Classical.positive_derivative_eventually_left_increment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:08:24.352035+00:00
-- url     : https://prove2.me/submissions/d01693b1-c1a4-4e05-b1a7-99c603d421ed

import Mathlib
open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), W (a - ε) < W a := by
  have h1 := hD.tendsto_slope
  have h2 : Tendsto (fun ε : ℝ => a - ε) (𝓝[>] 0) (𝓝[≠] a) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => a - ε) (𝓝 0) (𝓝 (a - 0)) := tendsto_const_nhds.sub tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [mem_compl_iff, mem_singleton_iff]; simp at hε ⊢; linarith
  have h3 := (h1.comp h2).eventually (lt_mem_nhds hd)
  filter_upwards [h3, self_mem_nhdsWithin] with ε hε hpos
  simp only [Function.comp, slope_def_field] at hε
  have hp : (0:ℝ) < ε := hpos
  have : a - ε - a = -ε := by ring
  rw [this] at hε
  by_contra hc
  push Not at hc
  have : (W (a - ε) - W a) / -ε ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  linarith
