-- Prove2me | solution 1 for Formalism.DivisionValues.phi_difference_le_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:42.274044+00:00
-- url     : https://prove2.me/submissions/03138e0f-9bb9-4dad-8151-d8c7f7a4c802

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution (y y' : ℝ) (h1 : 1 ≤ y') (h : y' ≤ y) :
    0 ≤ Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y' ∧ Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y' ≤ (y - y') * Real.log y := by
  have hy'0 : 0 < y' := by linarith
  have hy0 : 0 < y := by linarith
  have hy'ne : y' ≠ 0 := hy'0.ne'
  have hyne : y ≠ 0 := hy0.ne'
  simp only [Formalism.LatticeIndexTer.ph]
  have hl1 : Real.log y - Real.log y' ≤ y / y' - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hy'0)
    rwa [Real.log_div hyne hy'ne] at this
  have hl2 : Real.log y' - Real.log y ≤ y' / y - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hy'0 hy0)
    rwa [Real.log_div hy'ne hyne] at this
  have e1 : y' * (y / y') = y := by first | (field_simp; done) | (field_simp; ring) | (rw [mul_div_assoc']; exact mul_div_cancel_left₀ y hy'ne)
  have e2 : y * (y' / y) = y' := by first | (field_simp; done) | (field_simp; ring) | (rw [mul_div_assoc']; exact mul_div_cancel_left₀ y' hyne)
  have hly' : 0 ≤ Real.log y' := Real.log_nonneg h1
  have k1 := mul_le_mul_of_nonneg_left hl1 hy'0.le
  have k2 := mul_le_mul_of_nonneg_left hl2 hy0.le
  have k3 : 0 ≤ (y - y') * Real.log y' := mul_nonneg (by linarith) hly'
  constructor
  · linarith
  · linarith
end Formalism.DivisionValues
