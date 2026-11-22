-- Prove2me | solution 1 for Formalism.DivisionValues.R0.map_inv_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:25:18.829264+00:00
-- url     : https://prove2.me/submissions/6bae5792-9ac5-4fb2-b2ac-5277599fcdf9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.R0
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.DivisionValues.R0
theorem _root_.solution {F : Type} [Field F] (f : K →+* F) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ f.map_zero f.map_one]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [hdet, isUnit_iff_ne_zero, map_ne_zero f]
      rw [isUnit_iff_ne_zero] at h
      exact h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      Matrix.map_zero _ f.map_zero]
end Formalism.DivisionValues.R0
