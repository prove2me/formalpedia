-- Prove2me | solution 1 for CerednikDrinfeld.Omega.isExhausted_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b44d07e6-8fd4-5009-bd5b-a2365a264c81

import Theorems.Thm_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact
import Theorems.Thm_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_isExhausted_of_liesOverPrime

set_option autoImplicit false

open CerednikDrinfeld.Omega ValuationSubring

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (ϖ : PseudoUniformizer ↥(ratClosure A) A.valuation.Completion) :
    IsExhausted ϖ := by
  obtain ⟨ϖ', hϖ', hex, -⟩ :=
    exists_pseudoUniformizer_isExhausted_of_isCompact ↥(ratClosure A) A.valuation.Completion
      (isCompact_ratClosure_inter_closedBall_of_liesOverPrime r A hA) ϖ.ϖ ϖ.pos ϖ.lt_one
      (valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA).2.2

  have hϖeq : ϖ' = ϖ := by
    cases ϖ'; cases ϖ; cases hϖ'; rfl
  exact hϖeq ▸ hex

end S_CerednikDrinfeld_Omega_isExhausted_of_liesOverPrime
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_isExhausted_of_liesOverPrime (solution)
