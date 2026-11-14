-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_C1_moving_drift_chord_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:06:33.18018+00:00
-- url     : https://prove2.me/submissions/6e8245f3-5edb-4066-9ac1-c14714802cdd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem solution
    (w : ℝ → ℝ) (y d : ℝ) (x m h : ℕ → ℝ)
    (hw : ContDiffAt ℝ 1 w y)
    (hx : Tendsto x atTop (𝓝 y))
    (hm : Tendsto m atTop (𝓝 0)) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ n, h n ≠ 0) :
    Tendsto (fun n => (w (x n + d * h n - m n) - w (x n - m n)) / h n)
      atTop (𝓝 (d * deriv w y)) := by
  by_cases hd : d = 0
  · subst d
    simpa only [zero_mul, add_zero, sub_self, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  let r (n : ℕ) := x n + d * h n - m n
  let l (n : ℕ) := x n - m n
  have hdlim : Tendsto (fun _ : ℕ => d) atTop (𝓝 d) := tendsto_const_nhds
  have hr : Tendsto r atTop (𝓝 y) := by
    simpa only [mul_zero, add_zero, sub_zero] using
      (hx.add (hdlim.mul hh)).sub hm
  have hl : Tendsto l atTop (𝓝 y) := by
    simpa only [sub_zero] using hx.sub hm
  have hgap (n : ℕ) : r n - l n = d * h n := by
    dsimp only [r, l]
    ring
  have hs : (fun p : ℝ × ℝ =>
      w p.1 - w p.2 - (p.1 - p.2) * deriv w y) =o[𝓝 (y, y)]
        (fun p : ℝ × ℝ => p.1 - p.2) := by
    simpa using hasStrictFDerivAt_iff_isLittleO.mp
      (hasStrictDerivAt_iff_hasStrictFDerivAt.mp
        (ContDiffAt.hasStrictDerivAt hw (by norm_num)))
  have herror : Tendsto (fun n =>
      (w (r n) - w (l n) - (r n - l n) * deriv w y) / (r n - l n))
      atTop (𝓝 0) :=
    (hs.comp_tendsto (hr.prodMk_nhds hl)).tendsto_div_nhds_zero
  have hscaled : Tendsto (fun n => d *
      ((w (r n) - w (l n) - (r n - l n) * deriv w y) / (r n - l n)) +
        d * deriv w y) atTop (𝓝 (d * deriv w y)) := by
    simpa only [mul_zero, zero_add] using
      (hdlim.mul herror).add_const (d * deriv w y)
  apply hscaled.congr'
  filter_upwards [] with n
  change d * ((w (r n) - w (l n) - (r n - l n) * deriv w y) /
      (r n - l n)) + d * deriv w y = (w (r n) - w (l n)) / h n
  rw [hgap]
  field_simp [hd, hne n]
  ring
