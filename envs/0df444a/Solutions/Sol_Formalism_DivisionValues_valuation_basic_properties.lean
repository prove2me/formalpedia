-- Prove2me | solution 1 for Formalism.DivisionValues.valuation_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:36.751699+00:00
-- url     : https://prove2.me/submissions/c2792b6f-9ce6-4778-b0a5-f2599172bb33

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_conjPl_conjPl
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int_nonneg
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_star
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_lw_conjPl

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
theorem _root_.solution : ValBasic := by
  intro K _ _ _ w
  exact ⟨fun a b ha hb => vw_mul w a b ha hb, vw_star w, lw_conjPl w, conjPl_conjPl w,
    vw_one w, vw_inv w, vw_int_nonneg w⟩
end Formalism.DivisionValues
