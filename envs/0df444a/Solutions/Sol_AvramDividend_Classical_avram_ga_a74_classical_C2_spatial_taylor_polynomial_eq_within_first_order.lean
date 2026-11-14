-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a74_classical_C2_spatial_taylor_polynomial_eq_within_first_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:02:27.365209+00:00
-- url     : https://prove2.me/submissions/23cd5ee3-7173-43b1-be30-f1983c3eb89a

import Mathlib.Analysis.Calculus.Taylor
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- At distinct real positive spatial source states, the first order within-interval Taylor polynomial uses the ordinary classical derivative. -/
theorem solution (w : ℝ → ℝ) (y z : ℝ)
    (hyz : y ≠ z) (hw : DifferentiableAt ℝ w y) :
    taylorWithinEval w 1 (uIcc y z) y z =
      w y + deriv w y * (z - y) := by
  have hu : UniqueDiffWithinAt ℝ (uIcc y z) y :=
    (uniqueDiffOn_uIcc hyz) y left_mem_uIcc
  have hd : derivWithin w (uIcc y z) y = deriv w y :=
    hw.derivWithin hu
  rw [show (1 : ℕ) = 0 + 1 by decide, taylorWithinEval_succ]
  simp only [taylor_within_zero_eval, zero_add, iteratedDerivWithin_one]
  rw [hd]
  ring
