-- Prove2me | solution 1 for CohnElkies.tendsto_log_factorial_div_nat_sub_log_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/2ad8aa60-d761-4a27-a8aa-0650a1fc0a0b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_log_factorialStirlingSequence_div_nat
import Theorems.Thm_CohnElkies_tendsto_log_two_mul_nat_div_nat

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto
      (fun k : ℕ =>
        Real.log (k.factorial : ℝ) / (k : ℝ) - Real.log (k : ℝ))
      atTop (nhds (-1)) := by
  have hlimit :=
    (tendsto_log_factorialStirlingSequence_div_nat.add
      (tendsto_log_two_mul_nat_div_nat.const_mul (1 / 2 : ℝ))).sub
        (tendsto_const_nhds (x := (1 : ℝ)))
  have htarget :
      Tendsto
        (fun k : ℕ =>
          Real.log (Stirling.stirlingSeq k) / (k : ℝ) +
            (1 / 2 : ℝ) *
              (Real.log ((2 : ℝ) * (k : ℝ)) / (k : ℝ)) - 1)
        atTop (nhds (-1)) := by
    convert! hlimit using 1; norm_num
  refine htarget.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hformula := Stirling.log_stirlingSeq_formula k
  rw [Real.log_div hkreal (Real.exp_ne_zero 1), Real.log_exp]
    at hformula
  have hcomm :
      Real.log ((k : ℝ) * 2) = Real.log (2 * (k : ℝ)) := by
    rw [mul_comm]
  field_simp
  nlinarith [hformula, hcomm]
end CohnElkies
