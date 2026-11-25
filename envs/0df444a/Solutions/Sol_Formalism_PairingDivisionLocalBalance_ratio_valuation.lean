-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.ratio_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:23.106726+00:00
-- url     : https://prove2.me/submissions/a2b32e29-87f6-4677-85b9-a27a5655103d

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementX
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution : RatioVal := by
  intro K _ _ _ w a a' g ha ha'
  rw [div_eq_mul_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w a a'⁻¹ ha (inv_ne_zero ha'), Formalism.DivisionValues.ValuationRepresentative.vw_inv]
  ring
end Formalism.PairingDivisionLocalBalance
