-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_word_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:52:40.423173+00:00
-- url     : https://prove2.me/submissions/ddf16f0d-db9c-4e15-90b3-2e22a5486e7a

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_top_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_word
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_one_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_chebyshev_bound_sharp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.LiftWordCheb := by
  intro R M _ _ _ _ _ _ Ξ n s K dat A₀ A₀v e t t' α β X X' B hs hs0 he _ hA hA₀ h1 h2 hαβ hB
  have hch := fun a => chebyshev_bound_sharp (α a) (β a) (2 * n + s) (hαβ a) (by omega)
  have hb := WordLiftInduction.bound Ξ (2 * n + s) K dat (fun a => e a * (1 / t a - 1 / t' a))
    (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) X X' _ B
    (WordLiftInduction.word Ξ (2 * n + s) X X' K dat _ _ fun a Q Q' =>
      WordLiftInduction.top_eq_sum (WordLiftInduction.one_lift Ξ n s (dat a) (A₀ a) (A₀v a) (e a) (t a) (t' a) X X' (hs0 a)
        (he a) (hA a) (hA₀ a) (h1 a) (h2 a) Q Q') _ (hch a).1)
    (fun a => (hch a).2) hB
  have hn : ∀ a, ‖e a * (1 / t a - 1 / t' a)‖ = ‖1 / t a - 1 / t' a‖ := by
    intro a
    rw [norm_mul]
    rcases he a with h | h <;> simp [h]
  simpa only [hn] using hb
end Formalism.FourierDecayAlt.P
