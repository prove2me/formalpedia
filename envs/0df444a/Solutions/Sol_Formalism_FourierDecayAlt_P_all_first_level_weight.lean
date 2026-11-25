-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.all_first_level_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:36:47.728013+00:00
-- url     : https://prove2.me/submissions/fd7b819c-f282-4d15-bb34-17fa712aa316

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_word_weight_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.ProductFactorBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.AllFirstWeight := by
  intro K _ q x w Y h hp
  rw [word_weight_formula K q x w Y h]
  congr 1
  clear h
  induction w with
  | nil => simp
  | cons l w ih =>
    have hw := ih (fun g hg => hp g (by simp [hg]))
    have hl : l.first = true := hp l (by simp)
    cases hpl : l.plus
    · have e : wFactor l Y = 1 - 1 / (l.pt - Y - 1) ^ 2 := by simp [wFactor, hpl, hl]
      rw [List.map_cons, List.prod_cons, hw, e, List.filter_cons_of_pos (by simp [hpl]),
        List.map_cons, List.prod_cons]
    · have e : wFactor l Y = 1 := by simp [wFactor, hpl, hl]
      rw [List.map_cons, List.prod_cons, hw, e, one_mul, List.filter_cons_of_neg (by simp [hpl])]
end Formalism.FourierDecayAlt.P
