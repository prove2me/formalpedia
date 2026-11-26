-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.shifted_terminal_majorant_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:23.618996+00:00
-- url     : https://prove2.me/submissions/68eeb5ab-63fa-46b3-9130-6f208001dda2

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_natPow_rpow_eq_rpow_natPow

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} {r n : ℕ} (hr : 0 < r) :
    pi ^ r * (1 - pi) ^ n *
          ((n + r - 1).choose (r - 1) : ℝ) *
          realTerminalSpendTerm theta r (n + r) =
      (3 : ℝ) ^ (-theta) *
        (((3 : ℝ) ^ theta * pi / (2 : ℝ) ^ theta) ^ r) *
        (((n + r - 1).choose (r - 1) : ℝ) *
          centralReverseTailRatio theta pi ^ n) := by
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hthree : (0 : ℝ) ≤ 3 := by norm_num
  have htwoPos : (0 : ℝ) < (2 : ℝ) ^ theta := by positivity
  have hthreePos : (0 : ℝ) < (3 : ℝ) ^ theta := by positivity
  rw [show n + r = r + n by omega]
  unfold realTerminalSpendTerm centralReverseTailRatio
  rw [pow_add, Real.mul_rpow (by positivity) (by positivity),
    natPow_rpow_eq_rpow_natPow htwo,
    natPow_rpow_eq_rpow_natPow htwo]
  have hthreeNe : (3 : ℝ) ^ theta ≠ 0 := hthreePos.ne'
  have hpowThree :
      ((3 : ℝ) ^ theta) ^ (r - 1) =
        ((3 : ℝ) ^ theta) ^ r / (3 : ℝ) ^ theta := by
    calc
      ((3 : ℝ) ^ theta) ^ (r - 1) =
          (((3 : ℝ) ^ theta) ^ (r - 1) * (3 : ℝ) ^ theta) /
            (3 : ℝ) ^ theta := by field_simp
      _ = ((3 : ℝ) ^ theta) ^ r / (3 : ℝ) ^ theta := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
  rw [hpowThree, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  simp_rw [div_pow]
  field_simp [htwoPos.ne', hthreeNe] <;> ring
end CollatzEndpointTransport.FixedTotal
