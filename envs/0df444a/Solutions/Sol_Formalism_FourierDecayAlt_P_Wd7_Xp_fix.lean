-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.Xp_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:00.755061+00:00
-- url     : https://prove2.me/submissions/2c4c8c8a-023e-4b60-b692-f0189c4fd792

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Rh0_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_col

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
theorem _root_.solution (w : List (Letter K S)) (Y : K) (hr : Reg w Y) (k : Fin 2) (z : Ix S) :
    (Xp w Y k 0 : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0 := by
  induction w generalizing k z with
  | nil =>
    simp only [Xp, Matrix.one_apply]
    by_cases hk : k = 0
    · simp [hk, Matrix.one_apply]
    · simp [hk]
  | cons l w ih =>
    have hr' : Reg w Y := fun l' hl' => hr l' (List.mem_cons_of_mem _ hl')
    by_cases h : l.plus
    · have hl : Y - l.pt ≠ 1 := by
        have := hr l List.mem_cons_self
        simpa [RegL, h] using this
      simp only [Xp, h, if_true]
      rw [mul_col _ _ (Rh0_col l.intersection_update_fsHerm_neg_one _ hl)]
      exact ih hr' k z
    · simp only [Xp, h]
      exact ih hr' k z
end Formalism.FourierDecayAlt.P.Wd7
