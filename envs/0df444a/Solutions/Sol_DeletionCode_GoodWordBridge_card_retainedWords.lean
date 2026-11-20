-- Prove2me | solution 1 for DeletionCode.GoodWordBridge.card_retainedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:07:25.74021+00:00
-- url     : https://prove2.me/submissions/d1d12f29-288f-40af-84b3-97df9739b253

import Definitions.Def_DeletionCode_CodeSelection
import Definitions.Def_DeletionCode_UniqueWordCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_GoodWordBridge
import Theorems.Thm_DeletionCode_GoodWordBridge_retainedWords_eq_image_goodVertices

set_option autoImplicit true
open DeletionCode DeletionCode.GoodWordBridge
open Windows HeaderRecovery SignedSupport CircleHash ConflictGraphWitness
open ExceptionalProbability ObstructionProbability BipartiteSelection
variable {n : ℕ}
namespace DeletionCode.GoodWordBridge
theorem _root_.solution (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ) :
    (retainedWords (n := n) t k Q weights).card =
      (goodVertices (graph (n := n) t Q (realWeightedHash weights))).card := by
  classical
  rw [retainedWords_eq_image_goodVertices]
  apply Finset.card_image_iff.mpr
  intro v _hv w _hw hval
  exact Subtype.ext hval
end DeletionCode.GoodWordBridge
