-- Prove2me | solution 1 for FirstPassageLinearTransport.one_div_two_pow_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:16:30.642866+00:00
-- url     : https://prove2.me/submissions/be9b7480-cf4f-49bd-a144-09db6abac60b

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (q : ℕ) :
    1 / (2 : ℝ) ^ q = Real.exp (-(Real.log 2 * (q : ℝ))) := by
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  calc
    1 / (2 : ℝ) ^ q = 1 / (Real.exp (Real.log 2)) ^ q := by rw [htwo]
    _ = (Real.exp (Real.log 2) ^ q)⁻¹ := by rw [one_div]
    _ = Real.exp (-((q : ℝ) * Real.log 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
    _ = Real.exp (-(Real.log 2 * (q : ℝ))) := by ring_nf
end FirstPassageLinearTransport
