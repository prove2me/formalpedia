-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.common_gram_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:10:47.979212+00:00
-- url     : https://prove2.me/submissions/47ea3534-4609-4176-b3cd-d8dbe75da13b

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
import Theorems.Thm_DeletionCode_GeneratingBlocks_nonzero_incident

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {I : Type*} {L : ℕ} (G : I → Gram L → ℤ)
    (i j : I) (g : Gram L) (hi : G i g ≠ 0) (hj : G j g ≠ 0) :
    Adjacent G i j :=
  ⟨gramPrefix g, nonzero_incident (G i) g hi, nonzero_incident (G j) g hj⟩
end DeletionCode.GeneratingBlocks
