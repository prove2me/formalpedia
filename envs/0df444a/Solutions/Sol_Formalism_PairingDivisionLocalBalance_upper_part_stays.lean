-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.upper_part_stays
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:33.301097+00:00
-- url     : https://prove2.me/submissions/26cabebb-e6c2-4751-9812-226514eedf13

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementX
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_prod
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
theorem _root_.solution : UpperStays := by
  intro K _ _ _ w P R y y' e B hy hyy he hB
  have hy' : y' ≠ 0 := by intro h0; rw [h0, zero_mul] at hyy; exact hy hyy
  have hp : ∏ q ∈ R, e q ≠ 0 := by intro h0; rw [h0, mul_zero] at hyy; exact hy hyy
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w y' _ hy' hp
  rw [← hyy, vw_prod w R e (fun q hq => (Finset.prod_ne_zero_iff.mp hp) q hq)] at h1
  have h2 : 0 ≤ ∑ q ∈ R, vw w (e q) := Finset.sum_nonneg he
  have h3 : vw w y' ≤ vw w y := by omega
  exact le_trans (by exact_mod_cast h3) hB
end Formalism.PairingDivisionLocalBalance
