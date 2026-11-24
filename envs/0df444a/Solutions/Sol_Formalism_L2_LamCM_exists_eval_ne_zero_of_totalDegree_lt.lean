-- Prove2me | solution 1 for Formalism.L2.LamCM.exists_eval_ne_zero_of_totalDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:13:45.279203+00:00
-- url     : https://prove2.me/submissions/77561291-b5e4-4484-b7d1-6692fa7356df

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution {k σ : Type} [Field k] [Finite σ] (p : MvPolynomial σ k) (hp : p ≠ 0)
    (S : Finset k) (hS : p.totalDegree < S.card) : ∃ x : σ → k, eval x p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hp (eq_zero_of_eval_zero_at_prod_finset p (fun _ => S)
    (fun i => lt_of_le_of_lt (degreeOf_le_totalDegree p i) hS) (fun x _ => h x))
end Formalism.L2.LamCM
