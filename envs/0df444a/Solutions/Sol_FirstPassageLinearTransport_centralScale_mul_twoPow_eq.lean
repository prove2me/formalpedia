-- Prove2me | solution 1 for FirstPassageLinearTransport.centralScale_mul_twoPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:25.200815+00:00
-- url     : https://prove2.me/submissions/31e80268-2799-4390-a59e-84592529754d

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_two_rpow_neg_gap


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (q : ℕ) (t : ℝ) :
    centralOrbitScale q * (((2 ^ q : ℕ) : ℝ) ^ (1 - t)) =
      (2 : ℝ) ^ ((a0 - t) * (q : ℝ)) := by
  rw [centralOrbitScale_eq_two_rpow_neg_gap, Nat.cast_pow,
    show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  unfold driftGap
  congr 1
  ring
end FirstPassageLinearTransport
