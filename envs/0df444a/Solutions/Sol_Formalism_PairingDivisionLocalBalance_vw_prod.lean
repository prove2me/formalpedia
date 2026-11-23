-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.vw_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:08.866258+00:00
-- url     : https://prove2.me/submissions/7fd60d98-74b8-451a-8468-b5aaf3397ed1

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementX
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one


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
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) {P : Type} (R : Finset P)
    (e : P → K) (he : ∀ q ∈ R, e q ≠ 0) : vw w (∏ q ∈ R, e q) = ∑ q ∈ R, vw w (e q) := by
  classical
  induction R using Finset.induction_on with
  | empty => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (he a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun q hq => he q (Finset.mem_insert_of_mem hq)),
      ih fun q hq => he q (Finset.mem_insert_of_mem hq)]
end Formalism.PairingDivisionLocalBalance
