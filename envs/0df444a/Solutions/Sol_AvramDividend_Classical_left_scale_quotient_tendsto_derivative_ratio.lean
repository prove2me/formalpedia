-- Prove2me | solution 1 for AvramDividend.Classical.left_scale_quotient_tendsto_derivative_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:08:31.711114+00:00
-- url     : https://prove2.me/submissions/98b0592e-769b-4677-a34f-ab29ad68228f

import Mathlib
open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : d ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => W (a - ε) / (ε⁻¹ * (W a - W (a - ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (W a / d)) := by
  have h1 := hD.tendsto_slope
  have hc : Tendsto (fun ε : ℝ => a - ε) (𝓝 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).sub (tendsto_id (x := 𝓝 (0:ℝ)))
  have h2 : Tendsto (fun ε : ℝ => a - ε) (𝓝[>] 0) (𝓝[≠] a) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hc.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp at hε ⊢; linarith
  have h3 : Tendsto (fun ε : ℝ => ε⁻¹ * (W a - W (a - ε))) (𝓝[>] 0) (𝓝 d) := by
    refine (h1.comp h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hp : (0:ℝ) < ε := hε
    simp only [Function.comp, slope_def_field]
    have : a - ε - a = -ε := by ring
    rw [this]; field_simp; ring
  have h4 : Tendsto (fun ε : ℝ => W (a - ε)) (𝓝[>] 0) (𝓝 (W a)) :=
    (hD.continuousAt.tendsto.comp hc).mono_left nhdsWithin_le_nhds
  exact h4.div h3 hd
