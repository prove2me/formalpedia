-- Prove2me | solution 1 for Formalism.DivisionValues.finite_sum_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:04.978994+00:00
-- url     : https://prove2.me/submissions/823bc13d-ef09-4b27-9354-4e31f5f9239b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_conjPl_conjPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open ValuationRepresentative
namespace Formalism.DivisionValues
theorem _root_.solution : FinsumConj := by
  intro K _ _ _ f
  exact finsum_comp_equiv (Function.Involutive.toPerm _ (fun w => conjPl_conjPl w))
end Formalism.DivisionValues
