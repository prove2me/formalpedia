-- Prove2me | solution 1 for Formalism.GM.TM.setTies_deg_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:24.463047+00:00
-- url     : https://prove2.me/submissions/11bcb475-17db-4ef9-9f93-b6b9eedb5ce4

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

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
theorem _root_.solution (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n' i) (a : Fin N) :
    (LL.setTies T n).deg a ≤ (LL.setTies T n').deg a := by
  unfold Letters.setTies
  dsimp only
  split_ifs with h
  · exact hn _
  · exact le_rfl
end Formalism.GM.TM
