-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.plane_wave_word_chebyshev_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:30.980264+00:00
-- url     : https://prove2.me/submissions/d2986990-49a7-49b2-a2df-f3b9dac7b506

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_top_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_word
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_one_planeWave
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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.PlaneWaveWordCheb := by
  intro R M _ _ _ _ _ _ Ξ n K dat α β X X' B hn hαβ hsh hB
  have hch := fun a => chebyshev_bound_sharp (α a) (β a) (2 * n) (hαβ a) (by omega)
  exact WordLiftInduction.bound Ξ (2 * n) K dat (fun a => (dat a).s)
    (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) X X' _ B
    (WordLiftInduction.word Ξ (2 * n) X X' K dat _ _ fun a Q Q' =>
      WordLiftInduction.top_eq_sum (WordLiftInduction.one_planeWave Ξ n (dat a) (Q • X) (Q' • X') (hsh a).1 (hsh a).2) _
        (hch a).1)
    (fun a => (hch a).2) hB
end Formalism.FourierDecayAlt.P
