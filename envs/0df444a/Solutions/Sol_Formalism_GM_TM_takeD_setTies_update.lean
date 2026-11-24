-- Prove2me | solution 1 for Formalism.GM.TM.takeD_setTies_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:10.768814+00:00
-- url     : https://prove2.me/submissions/18f6b884-0c3c-4366-b635-cff2c3ebe503

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_letters_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {N : ℕ}
namespace Formalism.GM.TM
theorem _root_.solution (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) (i : Fin T.t) (x : ℕ) :
    (LL.setTies T (Function.update n i x)).takeD (T.pos i + 1) = (LL.setTies T n).takeD (T.pos i + 1) := by
  refine letters_ext rfl ?_
  funext a
  simp only [Letters.takeD, Letters.setTies]
  split_ifs with h1 h2
  · apply Function.update_of_ne
    intro heq
    have := Classical.choose_spec h2
    rw [heq] at this
    have := a.isLt
    simp at this; omega
  · rfl
  · rfl
end Formalism.GM.TM
