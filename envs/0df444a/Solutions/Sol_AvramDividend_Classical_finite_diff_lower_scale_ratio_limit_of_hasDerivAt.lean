-- Prove2me | solution 1 for AvramDividend.Classical.finite_diff_lower_scale_ratio_limit_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:05:46.194909+00:00
-- url     : https://prove2.me/submissions/9f0f1a51-2df5-4726-8fad-dc21165cd6bf

import Mathlib

open Filter Topology

theorem solution
    {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0:ℝ)) (𝓝[<] 0) := by
    have h1 : Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    exact tendsto_nhdsWithin_iff.2 ⟨h1, eventually_nhdsWithin_of_forall fun x hx => by
      simpa using (show (0:ℝ) < x from hx)⟩
  have hs := hD.tendsto_slope_zero_left.comp hneg
  have hslope : Tendsto (fun ε : ℝ => (W a - W (a - ε)) / ε) (𝓝[>] 0) (𝓝 (deriv W a)) := by
    refine hs.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
    have : ε ≠ 0 := ne_of_gt hε
    simp only [Function.comp_apply, smul_eq_mul, ← sub_eq_add_neg]
    field_simp
    ring
  have hcont : Tendsto (fun ε : ℝ => W (a - ε)) (𝓝[>] 0) (𝓝 (W a)) := by
    have : ContinuousAt (fun ε : ℝ => W (a - ε)) 0 := by
      have := hD.continuousAt
      exact ContinuousAt.comp (by simpa using this) (continuous_const.sub continuous_id).continuousAt
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  refine (hcont.div hslope hd).congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply]
  by_cases h : W a - W (a - ε) = 0
  · simp [h]
  · field_simp
