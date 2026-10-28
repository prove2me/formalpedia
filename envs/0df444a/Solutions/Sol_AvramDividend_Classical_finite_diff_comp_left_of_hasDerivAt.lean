-- Prove2me | solution 1 for AvramDividend.Classical.finite_diff_comp_left_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:54:01.643067+00:00
-- url     : https://prove2.me/submissions/9cba1e38-3b15-4c9b-b49e-9f27bfa02e31

import Mathlib

theorem solution {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) :
    Filter.Tendsto (fun ε : ℝ => W (a - ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) := by
  have hc : ContinuousAt (fun ε : ℝ => W (a - ε)) 0 := by
    apply ContinuousAt.comp (g := W) (f := fun ε : ℝ => a - ε)
    · simpa using hD.continuousAt
    · fun_prop
  have := hc.tendsto
  simp only [sub_zero] at this
  exact this.mono_left nhdsWithin_le_nhds
