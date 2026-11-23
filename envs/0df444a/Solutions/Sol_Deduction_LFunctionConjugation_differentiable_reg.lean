-- Prove2me | solution 1 for Deduction.LFunctionConjugation.differentiable_reg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:17.988508+00:00
-- url     : https://prove2.me/submissions/ecbe6b0a-77d5-4053-884b-dc6c895a4e4f

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj

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
open Deduction.LFunctionConjugation
open HurwitzZeta
namespace Deduction.LFunctionConjugation
theorem _root_.solution (a : UnitAddCircle) : Differentiable ℂ (reg a) := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact differentiableAt_hurwitzZeta_sub_one_div a
  · have e : reg a = fun z => hurwitzZeta a z - (z - 1)⁻¹ * (Gammaℝ z)⁻¹ := by
      funext z
      rw [reg, one_div, div_eq_mul_inv]
    rw [e]
    exact (differentiableAt_hurwitzZeta a hs).sub
      (((differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs)).mul
        (differentiable_Gammaℝ_inv s))
end Deduction.LFunctionConjugation
