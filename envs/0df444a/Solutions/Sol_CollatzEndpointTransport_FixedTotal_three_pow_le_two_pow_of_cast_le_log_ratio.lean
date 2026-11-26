-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.three_pow_le_two_pow_of_cast_le_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:30.358934+00:00
-- url     : https://prove2.me/submissions/62cc48db-ac8f-4cef-9646-a92d8502fa46

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ}
    (h : (s : ℝ) ≤ (Real.log 2 / Real.log 3) * N) :
    3 ^ s ≤ 2 ^ N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogs : (s : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right h hlog3.le
    field_simp [hlog3.ne'] at this
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogs
  have hreal : (3 : ℝ) ^ s ≤ (2 : ℝ) ^ N := by
    calc
      (3 : ℝ) ^ s = Real.exp ((s : ℝ) * Real.log 3) := by
        symm
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      _ ≤ Real.exp ((N : ℝ) * Real.log 2) := hexp
      _ = (2 : ℝ) ^ N := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hreal
end CollatzEndpointTransport.FixedTotal
