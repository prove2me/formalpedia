-- Prove2me | solution 1 for AvramDividend.Classical.finite_diff_upper_of_hasDerivAt_bridge_20261028
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:21:12.798127+00:00
-- url     : https://prove2.me/submissions/0cbfaa69-6c69-4512-ac47-0adef214df72

import Mathlib

theorem solution
    {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by
  have hs := hD.tendsto_slope_zero_right
  have hc : Filter.Tendsto (fun ε : ℝ => W (a + ε)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) := by
    have : Filter.Tendsto (fun ε : ℝ => W (a + ε)) (nhds 0) (nhds (W a)) := by
      have h1 : ContinuousAt (fun ε : ℝ => W (a + ε)) 0 :=
        ((show HasDerivAt W (deriv W a) (a + 0) by simpa using hD).comp_const_add a 0).continuousAt
      simpa using h1.tendsto
    exact this.mono_left nhdsWithin_le_nhds
  refine (hc.div hs hd).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.div_apply, smul_eq_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  ring
