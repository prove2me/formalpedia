-- Prove2me | solution 1 for AvramDividend.Classical.finite_diff_lower_of_hasDerivAt_bridge_20261028
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:21:27.615427+00:00
-- url     : https://prove2.me/submissions/465afaf8-52a6-488a-9c0d-021c251c05a7

import Mathlib

theorem solution
    {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by
  have hg : HasDerivAt (fun t : ℝ => W (a - t)) (-(deriv W a)) 0 := by
    exact (show HasDerivAt W (deriv W a) (a - 0) by simpa using hD).comp_const_sub a 0
  have hs := hg.tendsto_slope_zero_right
  simp only [zero_add, sub_zero] at hs
  have hc : Filter.Tendsto (fun ε : ℝ => W (a - ε)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) := by
    have : Filter.Tendsto (fun ε : ℝ => W (a - ε)) (nhds 0) (nhds (W a)) := by
      have h1 : ContinuousAt (fun ε : ℝ => W (a - ε)) 0 := hg.continuousAt
      simpa using h1.tendsto
    exact this.mono_left nhdsWithin_le_nhds
  have hs' := hs.neg
  rw [neg_neg] at hs'
  refine (hc.div hs' hd).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.div_apply, smul_eq_mul]
  rw [show -(ε⁻¹ * (W (a - ε) - W a)) = ε⁻¹ * (W a - W (a - ε)) by ring]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  ring
