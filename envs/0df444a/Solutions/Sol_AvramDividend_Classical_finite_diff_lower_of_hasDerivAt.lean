-- Prove2me | solution 1 for AvramDividend.Classical.finite_diff_lower_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:54:20.659585+00:00
-- url     : https://prove2.me/submissions/07a7129d-251d-44ba-a2c6-d08584c4a6bb

import Mathlib

theorem solution {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
        simpa using (continuous_neg (G := ℝ)).tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa using hε
  have hs := hD.tendsto_slope_zero_left.comp hneg
  have hc : Filter.Tendsto (fun ε : ℝ => W (a - ε)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) := by
    have hc : ContinuousAt (fun ε : ℝ => W (a - ε)) 0 := by
      apply ContinuousAt.comp (g := W) (f := fun ε : ℝ => a - ε)
      · simpa using hD.continuousAt
      · fun_prop
    have := hc.tendsto
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := hc.div hs hd
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply, Function.comp_apply, smul_eq_mul]
  rw [← sub_eq_add_neg, show W (a - ε) - W a = -(W a - W (a - ε)) by ring]
  rcases eq_or_ne (W a - W (a - ε)) 0 with h | h
  · simp [h]
  · field_simp
