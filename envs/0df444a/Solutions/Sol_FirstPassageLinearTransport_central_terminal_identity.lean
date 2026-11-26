-- Prove2me | solution 1 for FirstPassageLinearTransport.central_terminal_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:35.42878+00:00
-- url     : https://prove2.me/submissions/44f71f37-3525-4949-a2f1-58c39cfb7a4d

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_two_rpow_neg_gap


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (eta : ℝ) (M : ℕ) :
    centralOrbitScale M * ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) =
      (2 : ℝ) ^ ((a0 + eta) * M + 1 + eta) := by
  rw [centralOrbitScale_eq_two_rpow_neg_gap,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1
  unfold driftGap
  push_cast
  ring
end FirstPassageLinearTransport
