-- Prove2me | solution 1 for FamousTheorems.hadamard_three_lines
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:21:02.191842+00:00
-- url     : https://prove2.me/submissions/00f537fa-f37b-43be-b39a-62615d7e78ac

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} {a b l u : ℝ} (hul : l < u)
    (hz : z.re ∈ Set.Icc l u) (hd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo l u))
    (hB : BddAbove ((fun w => ‖f w‖) '' (Complex.re ⁻¹' Set.Icc l u)))
    (ha : ∀ w : ℂ, w.re = l → ‖f w‖ ≤ a) (hb : ∀ w : ℂ, w.re = u → ‖f w‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) :=
  Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hul hz hd hB ha hb
