-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.entry_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:47.237406+00:00
-- url     : https://prove2.me/submissions/29cf3bb3-c238-4f5a-96bf-3bf4ddca58e3

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_transfer_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_RRw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_TTw_corner
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_entry_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_good_cons

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
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (hw : Good w) :
    RRw QQ w e1 e1 = (w.reverse.map fun l => QQ l.pt 0 0).prod := by
  induction w with
  | nil => simp [RRw]
  | cons l w ih =>
    obtain ⟨hg, hs, _, hr⟩ := good_cons hw
    have hM : FreeOf2 l.intersection_update_fsHerm_neg_one (if l.plus then TTw QQ w l.pt else (TTw QQ w l.pt)ᵀ) := by
      split_ifs
      · exact freeOf_transfer_word_matrix QQ w hs _
      · exact freeOf2_transpose (freeOf_transfer_word_matrix QQ w hs _)
    have h00 : (if l.plus then TTw QQ w l.pt else (TTw QQ w l.pt)ᵀ) 0 0 = TTw QQ w l.pt 0 0 := by
      split_ifs <;> rfl
    simp only [RRw]
    rw [entry_ins l.intersection_update_fsHerm_neg_one _ _ (free_RRw QQ w hs) hM, h00, Matrix.mul_apply]
    simp only [TTw_corner QQ w l.pt hg.1 hr]
    simp [ih hg]
end Formalism.FourierDecayAlt.P.Wd7
