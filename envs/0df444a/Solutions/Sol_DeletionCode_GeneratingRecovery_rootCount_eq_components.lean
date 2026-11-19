-- Prove2me | solution 1 for DeletionCode.GeneratingRecovery.rootCount_eq_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:58:18.260651+00:00
-- url     : https://prove2.me/submissions/79010326-5963-4bf3-bc83-20189903f411

import Definitions.Def_DeletionCode_GeneratingModel
import Definitions.Def_DeletionCode_ConcreteRecovery
import Definitions.Def_DeletionCode_SupportComponents
import Definitions.Def_DeletionCode_GeneratingRecovery

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingRecovery
open Windows HeaderRecovery GeneratingModel ConcreteDecoder
variable {B : Type*} {k : ℕ}
namespace DeletionCode.GeneratingRecovery
theorem _root_.solution [Fintype B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ConcreteInitialization.rootCount (model E x n hx hg) =
      Fintype.card (GeneratingModel.Components E) := by
  classical
  unfold ConcreteInitialization.rootCount
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (rootEquiv E x n hx hg)).symm
end DeletionCode.GeneratingRecovery
