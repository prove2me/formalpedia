-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_word_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:52:44.661486+00:00
-- url     : https://prove2.me/submissions/db66b600-aa9d-4c43-95ec-e97aa12e8841

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_top_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_liftLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_word_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.LiftWord := by
  unfold LiftWord
  intro R M _ _ _ _ _ _ Ξ n s K dat A₀ A₀v e t t' grid X X' hs1 hs0 he ht hA hA0 hB hBv hg
  have h := word_gen Ξ (2 * n + s) X X' K dat grid (fun a => e a * (1 / t a - 1 / t' a))
    (fun a Q Q' => top_extract (liftLetter Ξ n s (dat a) (A₀ a) (A₀v a) (e a) (t a) (t' a) (Q • X)
      (Q' • X') (hs0 a) (he a) (hA a).1 (hA a).2.1 (hA a).2.2.1 (hA a).2.2.2 (hA0 a).1 (hA0 a).2.1
      (hA0 a).2.2.1 (hA0 a).2.2.2
      (fun Y Y' => by
        have hh := hB a Y Q (evR (dat a).Av Y' * Q')
        rw [mul_smul (evR (dat a).Av Y') Q' X'] at hh
        exact hh)
      (fun Y Y' => by
        have hh := hBv a Y' (evR (dat a).A Y * Q) Q'
        rw [mul_smul (evR (dat a).A Y) Q X] at hh
        exact hh)) (grid a) (hg a)) 1 1
  simp only [one_smul] at h
  exact h
end Formalism.FourierDecayAlt.P
