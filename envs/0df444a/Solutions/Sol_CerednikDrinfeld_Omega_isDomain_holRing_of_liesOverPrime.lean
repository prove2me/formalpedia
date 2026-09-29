-- Prove2me | solution 1 for CerednikDrinfeld.Omega.isDomain_holRing_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/867726e9-a789-57bb-adbb-28ffd1de771b

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing
import Theorems.Thm_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_isDomain_holRing_of_liesOverPrime

set_option autoImplicit false

open CerednikDrinfeld.Omega ValuationSubring

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (ϖ : PseudoUniformizer ↥(ratClosure A) A.valuation.Completion) :
    IsDomain ↥(holRing ϖ) := by
  haveI : IsAlgClosed A.valuation.Completion :=
    ValuationSubring.isAlgClosed_completion_of_liesOverPrime r (Fact.out) A hA
  have hrk : ∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y :=
    (ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA).2.2
  obtain ⟨ϖ', hϖ', hex, hfin⟩ :=
    exists_pseudoUniformizer_isExhausted_of_isCompact (↥(ratClosure A)) A.valuation.Completion
      (ValuationSubring.isCompact_ratClosure_inter_closedBall_of_liesOverPrime r A hA) ϖ.ϖ ϖ.pos ϖ.lt_one hrk

  rcases ϖ with ⟨w, hw0, hw1, hws⟩
  rcases ϖ' with ⟨w', hw0', hw1', hws'⟩
  dsimp only at hϖ'
  subst hϖ'
  exact isDomain_holRing (↥(ratClosure A)) A.valuation.Completion _ hrk hex hfin

end S_CerednikDrinfeld_Omega_isDomain_holRing_of_liesOverPrime
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_isDomain_holRing_of_liesOverPrime (solution)
