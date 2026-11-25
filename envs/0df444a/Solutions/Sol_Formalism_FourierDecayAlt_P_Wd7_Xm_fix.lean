-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.Xm_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:18:42.077221+00:00
-- url     : https://prove2.me/submissions/c7674bca-5ae3-44c6-8ce0-50372ba45ac5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_negative_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Rht0_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (w : List (Letter K S)) (Y : K) (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : Reg w Y)
    (k : Fin 2) (z : Ix S) :
    (Xm w Y 0 k : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0 := by
  induction w generalizing k z with
  | nil =>
    simp only [Xm, Matrix.one_apply]
    by_cases hk : k = 0
    · simp [hk, Matrix.one_apply]
    · have hk' : ¬ (0 = k) := fun h => hk h.symm
      simp [hk, hk']
  | cons l w ih =>
    have hr' : Reg w Y := fun l' hl' => hr l' (List.mem_cons_of_mem _ hl')
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases h : l.plus
    · simp only [Xm, h, if_true]
      exact ih hn.2 hr' k z
    · have hl : l.pt - Y ≠ 1 := by
        have := hr l List.mem_cons_self
        simpa [RegL, h] using this
      rw [show (Xm (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * Xm w Y from by simp [Xm, h]]
      rw [Rht0_row l.intersection_update_fsHerm_neg_one _ hl _ (freeOf_negative_word_matrix w hn.1 Y)]
      exact ih hn.2 hr' k z
end Formalism.FourierDecayAlt.P.Wd7
