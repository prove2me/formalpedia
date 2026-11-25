-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.gaussValUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:14.149147+00:00
-- url     : https://prove2.me/submissions/63d3d40b-c4f1-4097-b2e6-188d41104dc2

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementX
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int_nonneg
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
theorem _root_.solution : GaussUnit := by
  intro K _ _ _ w G G' q hq h hv
  have hq0 : (q : K) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hG : (G : K) ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact hq0 h.symm
  have hG' : (G' : K) ≠ 0 := by intro h0; rw [h0, mul_zero] at h; exact hq0 h.symm
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (G : K) (G' : K) hG hG'
  rw [h, hv] at h1
  have h2 := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w G
  have h3 := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w G'
  omega
end Formalism.PairingDivisionLocalBalance
