-- Prove2me | solution 1 for DeletionCode.GeneratingRecovery.rootCount_eq_graph_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:59:05.819447+00:00
-- url     : https://prove2.me/submissions/f9ab5237-8329-4df9-8ad2-3895795db72a

import Definitions.Def_DeletionCode_GeneratingModel
import Definitions.Def_DeletionCode_ConcreteRecovery
import Definitions.Def_DeletionCode_SupportComponents
import Definitions.Def_DeletionCode_GeneratingRecovery
import Theorems.Thm_DeletionCode_GeneratingRecovery_rootCount_eq_components

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingRecovery
open Windows HeaderRecovery GeneratingModel ConcreteDecoder
variable {B : Type*} {k : ℕ}
namespace DeletionCode.GeneratingRecovery
theorem _root_.solution [Fintype B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ConcreteInitialization.rootCount (model E x n hx hg) =
      Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) := by
  rw [rootCount_eq_components E x n hx hg]
  exact Fintype.card_congr (componentGraphEquiv E)
end DeletionCode.GeneratingRecovery
