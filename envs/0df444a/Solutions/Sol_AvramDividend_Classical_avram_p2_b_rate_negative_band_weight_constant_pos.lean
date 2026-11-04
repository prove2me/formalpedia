-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_band_weight_constant_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:32:46.494591+00:00
-- url     : https://prove2.me/submissions/5bff90b4-49f5-4123-a93b-8debf0928903

import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    0 < (1 - Real.exp (-θ * ε)) ^ 4 := by
  have hneg : -θ * ε < 0 := by
    nlinarith [mul_pos hθ hε]
  have hexp : Real.exp (-θ * ε) < 1 :=
    Real.exp_lt_one_iff.mpr hneg
  exact pow_pos (by linarith) 4