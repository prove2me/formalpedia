-- Prove2me | solution 1 for Formalism.GM.TM.S_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:23.355923+00:00
-- url     : https://prove2.me/submissions/c03bfb6d-cec5-4947-b163-7c360f922052

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_setTies_deg_mono

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
theorem _root_.solution (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n' i) (i : Fin T.t) :
    T.S (LL.setTies T n) i ≤ T.S (LL.setTies T n') i := by
  unfold TieData.S
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact setTies_deg_mono LL T n n' hn a
  · exact le_rfl
end Formalism.GM.TM
