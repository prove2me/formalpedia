-- Prove2me | solution 1 for AvramDividend.Classical.renewal_scale_finite_difference_limits_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:24:42.839982+00:00
-- url     : https://prove2.me/submissions/561acbf5-4d79-4bc3-9e61-cf2dcb747971

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology
open scoped ENNReal


theorem solution
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : d ≠ 0) :
    Tendsto
      (fun ε : ℝ => ENNReal.ofReal
        (ε * W (a - ε) / (W a - W (a - ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (W a / d))) ∧
    Tendsto
      (fun ε : ℝ => ENNReal.ofReal
        (ε * W (a + ε) / (W (a + ε) - W a)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (W a / d))) := by
  have hcont : ContinuousAt W a := hD.continuousAt
  have hR : Tendsto (fun ε : ℝ => ε⁻¹ * (W (a + ε) - W a)) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    simpa [smul_eq_mul] using hD.tendsto_slope_zero_right
  have hL0 : Tendsto (fun t : ℝ => t⁻¹ * (W (a + t) - W a)) (𝓝[<] (0 : ℝ)) (𝓝 d) := by
    simpa [smul_eq_mul] using hD.tendsto_slope_zero_left
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    have := (continuous_neg.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (by simpa using this) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using hε
  have hL : Tendsto (fun ε : ℝ => ε⁻¹ * (W a - W (a - ε))) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    refine (hL0.comp hneg).congr (fun ε => ?_)
    simp only [Function.comp, sub_eq_add_neg, inv_neg]
    ring
  have hWm : Tendsto (fun ε : ℝ => W (a - ε)) (𝓝[>] (0 : ℝ)) (𝓝 (W a)) := by
    have h1 : Tendsto (fun ε : ℝ => a - ε) (𝓝 (0:ℝ)) (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).sub (tendsto_id (x := 𝓝 (0:ℝ)))
    exact (hcont.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  have hWp : Tendsto (fun ε : ℝ => W (a + ε)) (𝓝[>] (0 : ℝ)) (𝓝 (W a)) := by
    have h1 : Tendsto (fun ε : ℝ => a + ε) (𝓝 (0:ℝ)) (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).add (tendsto_id (x := 𝓝 (0:ℝ)))
    exact (hcont.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  constructor
  · apply ENNReal.tendsto_ofReal
    refine ((hWm.div hL hd)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := ne_of_gt hε
    by_cases h : W a - W (a - ε) = 0
    · simp [h]
    · simp only [Pi.div_apply]
      field_simp
  · apply ENNReal.tendsto_ofReal
    refine ((hWp.div hR hd)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := ne_of_gt hε
    by_cases h : W (a + ε) - W a = 0
    · simp [h]
    · simp only [Pi.div_apply]
      field_simp

