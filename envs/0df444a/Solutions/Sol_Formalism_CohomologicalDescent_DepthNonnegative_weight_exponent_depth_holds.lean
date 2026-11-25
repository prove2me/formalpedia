-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.weight_exponent_depth_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:12.454408+00:00
-- url     : https://prove2.me/submissions/5aa49e33-83b5-4377-a4b0-c6e5dd0c521d

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_depth_as_weight_sum_holds
import Theorems.Thm_Formalism_CohomologicalDescent_weightExchangeFull_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : WEDepth := by
  intro ι _ σ k j t q l h F _ _ W U U' bot cst kap c τ lam w hl ht hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    hU hU'
  have h := weightExchangeFull_holds ι σ k j t q l h F W U U' bot cst kap c τ hl ht hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11
  rw [depth_as_weight_sum_holds]
  have e1 : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j),
      (UN (k + j + t + q) lam a - ((w a : ℤ) + ((k + j + t + q : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ))) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U τ a - U' τ a) :=
    Finset.sum_congr rfl fun a _ => by rw [hU, hU']
  rw [e1]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring
end Formalism.CohomologicalDescent.DepthNonnegative
