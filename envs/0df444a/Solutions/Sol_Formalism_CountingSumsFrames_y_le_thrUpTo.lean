-- Prove2me | solution 1 for Formalism.CountingSumsFrames.y_le_thrUpTo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:56.701853+00:00
-- url     : https://prove2.me/submissions/bb82c9a2-4833-4a16-9b3e-05ba0f9deafb

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) :
    Y p (r := r) LL T.J T.thr ≤ Y p (r := r) LL T.J (T.thrUpTo i) := by
  apply inf_le_inf_left
  apply le_iInf
  intro k
  refine (iInf_le _ k).trans ?_
  unfold TieData.thrUpTo
  split_ifs
  · exact le_rfl
  · rw [ycond_top]; exact le_top
end Formalism.CountingSumsFrames
