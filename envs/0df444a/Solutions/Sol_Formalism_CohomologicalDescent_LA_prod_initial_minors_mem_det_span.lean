-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.prod_initial_minors_mem_det_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:53.522025+00:00
-- url     : https://prove2.me/submissions/90a07670-9677-4a91-b396-29d146f7f83e

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_T_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_T_xy
import Theorems.Thm_Formalism_CohomologicalDescent_LA_initial_minor_mem_det_span
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ 2) (I : ∀ k, Fin (sz k) → Fin 2)
    (S : Finset (Fin K)) :
    ∏ k ∈ S, initMinor ℤ (I k) (hsz k) ∈
      detPowMulMonomialSpan (∑ k ∈ S, if sz k = 2 then 1 else 0) (∑ k ∈ S, if sz k = 1 then 1 else 0) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    simpa [la_xy] using la_T_xy 0 0 0
  | @insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.sum_insert hk]
    exact la_T_mul (initial_minor_mem_det_span (sz k) (I k) (hsz k)) ih
end Formalism.CohomologicalDescent.LA
