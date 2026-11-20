-- Prove2me | solution 1 for DeletionCode.GeneratingRecovery.generating_decode_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:01:46.187393+00:00
-- url     : https://prove2.me/submissions/607a9b21-69e9-4395-9346-bc5d259b4a3c

import Definitions.Def_DeletionCode_GeneratingModel
import Definitions.Def_DeletionCode_ConcreteRecovery
import Definitions.Def_DeletionCode_SupportComponents
import Definitions.Def_DeletionCode_GeneratingRecovery
import Theorems.Thm_DeletionCode_GeneratingRecovery_rootCount_eq_graph_components
import Theorems.Thm_DeletionCode_ConcreteRecovery_decode_exists


set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingRecovery
open Windows HeaderRecovery GeneratingModel ConcreteDecoder
variable {B : Type*} {k : ℕ}
namespace DeletionCode.GeneratingRecovery
theorem _root_.solution [Fintype B] [DecidableEq B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ∃ roots instructions,
      roots.length = Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k E.header roots instructions =
        some (fun b i => negativePath k (E.header b) (E.long b) i.val) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode⟩ :=
    ConcreteRecovery.decode_exists (model E x n hx hg) hx
  exact ⟨roots, instructions,
    hroots.trans (rootCount_eq_graph_components E x n hx hg), hcost, hdecode⟩
end DeletionCode.GeneratingRecovery
