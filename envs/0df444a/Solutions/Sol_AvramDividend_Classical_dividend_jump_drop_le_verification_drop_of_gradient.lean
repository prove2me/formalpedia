-- Prove2me | solution 1 for AvramDividend.Classical.dividend_jump_drop_le_verification_drop_of_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:39:55.588637+00:00
-- url     : https://prove2.me/submissions/c02f6e5d-982c-419c-9cf7-2c603b80c51c

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open AvramDividend.Classical

/-- The marginal dividend inequality ensures a lump-sum dividend is
dominated by the verification-function drop over the paid interval. -/
theorem solution
    (w : ℝ → ℝ) (a d : ℝ) (hd : 0 ≤ d)
    (hwCont : ContinuousOn w (Icc (a - d) a))
    (hwDiff : DifferentiableOn ℝ w (interior (Icc (a - d) a)))
    (hwGrad : ∀ y ∈ interior (Icc (a - d) a), 1 ≤ deriv w y) :
    d ≤ w a - w (a - d) := by
  have hab : a - d ≤ a := by linarith
  have hMvt :=
    (convex_Icc (a - d) a).mul_sub_le_image_sub_of_le_deriv
      hwCont hwDiff hwGrad
      (a - d) (Set.left_mem_Icc.mpr hab)
      a (Set.right_mem_Icc.mpr hab) hab
  nlinarith only [hMvt]
