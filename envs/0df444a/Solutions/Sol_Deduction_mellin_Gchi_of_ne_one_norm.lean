-- Prove2me | solution 1 for Deduction.mellin_Gchi_of_ne_one_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:03.028825+00:00
-- url     : https://prove2.me/submissions/ea0af230-08cf-4d1d-b18c-85c4735410d5

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_MellinRamp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne
import Theorems.Thm_Deduction_mellin_ramp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ‖((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)‖ =
      (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
  have h := mellin_ramp n hn (s.re : ℂ) (by simpa using hs)
  apply ofReal_injective
  rw [← integral_complex_ofReal, ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
    Real.norm_of_nonneg (le_max_right _ _)]
  change (((max (y / n - 1) 0 * y ^ (-s - 1).re : ℝ)) : ℂ) = _
  rw [ofReal_mul, ofReal_cpow hy0.le]
  simp
end Deduction
