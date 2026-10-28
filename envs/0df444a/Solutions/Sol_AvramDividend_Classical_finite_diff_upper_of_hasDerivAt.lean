-- Prove2me | solution 1 for AvramDividend.Classical.finite_diff_upper_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:54:13.305824+00:00
-- url     : https://prove2.me/submissions/6b23f266-ef99-4234-9d0d-ab641d0d61f8

import Mathlib

theorem solution {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by
  have hs := hD.tendsto_slope_zero_right
  have hc : Filter.Tendsto (fun ε : ℝ => W (a + ε)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) := by
    have hc : ContinuousAt (fun ε : ℝ => W (a + ε)) 0 := by
      apply ContinuousAt.comp (g := W) (f := fun ε : ℝ => a + ε)
      · simpa using hD.continuousAt
      · fun_prop
    have := hc.tendsto
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := hc.div hs hd
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply, Pi.mul_apply, Pi.inv_apply, Function.comp_apply, smul_eq_mul]
  rcases eq_or_ne (W (a + ε) - W a) 0 with h | h
  · simp [h]
  · field_simp
