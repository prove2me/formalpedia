-- Prove2me | solution 1 for AvramDividend.Classical.finite_diff_upper_scale_ratio_limit_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:19:18.75495+00:00
-- url     : https://prove2.me/submissions/01d8b062-8f14-4e90-9a4d-d0c247a000c5

import Mathlib
open Filter Topology
theorem solution
    {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by
  have hs := hD.tendsto_slope_zero_right
  have hslope : Tendsto (fun ε : ℝ => (W (a + ε) - W a) / ε) (𝓝[>] 0) (𝓝 (deriv W a)) := by
    refine hs.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
    simp only [smul_eq_mul]
    rw [div_eq_inv_mul]
  have hcont : Tendsto (fun ε : ℝ => W (a + ε)) (𝓝[>] 0) (𝓝 (W a)) := by
    have : ContinuousAt (fun ε : ℝ => W (a + ε)) 0 := by
      have := hD.continuousAt
      exact ContinuousAt.comp (by simpa using this) (continuous_const.add continuous_id).continuousAt
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  refine (hcont.div hslope hd).congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply]
  by_cases h : W (a + ε) - W a = 0
  · simp [h]
  · field_simp
