-- Prove2me | solution 1 for Deduction.mellin_Gchi_modOne_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:21.181558+00:00
-- url     : https://prove2.me/submissions/3d6a6108-f8a7-49e9-af78-e04e0e7a6d9e

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_MellinRamp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiModOne
import Theorems.Thm_Deduction_mellin_Gchi_modOne_log_int

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
theorem _root_.solution (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
  have ha : (-s).re < -1 := by simp; linarith
  have hs1 : -s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨hi, ht⟩ := mellin_Gchi_modOne_log_int s hs
  have hd : ∀ y ∈ Ici (1 : ℝ), HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1))
      ((-s + 1) * (((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) + (y : ℂ) ^ (-s)) y := by
    intro y hy
    have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
    refine ((Real.hasDerivAt_log hy0).ofReal_comp.mul
      (hasDerivAt_ofReal_cpow_const hy0 hs1)).congr_deriv ?_
    rw [add_sub_cancel_right, cpow_add _ _ hyC, cpow_one]
    push_cast
    field_simp
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((hi.const_mul _).add (integrableOn_Ioi_cpow_of_lt ha zero_lt_one)) ht
  rw [integral_add (hi.const_mul _) (integrableOn_Ioi_cpow_of_lt ha zero_lt_one),
    integral_const_mul, integral_Ioi_cpow_of_lt ha zero_lt_one] at h
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_mul, sub_zero] at h
  have e2 : (s - 1) ^ 2 = (-s + 1) ^ 2 := by ring
  rw [e2]
  field_simp at h ⊢
  linear_combination h
end Deduction
