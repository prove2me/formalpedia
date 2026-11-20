-- Prove2me | solution 1 for DeletionCode.GoodWordBridge.retainedWords_eq_image_goodVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:03:55.003845+00:00
-- url     : https://prove2.me/submissions/8647fb99-53eb-4721-9c3a-301d0a0e65d1

import Definitions.Def_DeletionCode_CodeSelection
import Definitions.Def_DeletionCode_UniqueWordCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_GoodWordBridge
import Theorems.Thm_DeletionCode_GoodWordBridge_mem_retainedWords_iff
import Theorems.Thm_DeletionCode_BipartiteSelection_mem_goodVertices
attribute [local simp] DeletionCode.BipartiteSelection.mem_goodVertices



set_option autoImplicit true
open DeletionCode DeletionCode.GoodWordBridge
open Windows HeaderRecovery SignedSupport CircleHash ConflictGraphWitness
open ExceptionalProbability ObstructionProbability BipartiteSelection
variable {n : ℕ}
namespace DeletionCode.GoodWordBridge
theorem _root_.solution (t k Q : ℕ)
    (weights : Gram (windowLength k) → ℝ) :
    retainedWords (n := n) t k Q weights =
      (goodVertices (graph (n := n) t Q (realWeightedHash weights))).image Subtype.val := by
  classical
  ext x
  rw [mem_retainedWords_iff]
  constructor
  · rintro ⟨v, hv, hgood⟩
    exact Finset.mem_image.mpr ⟨v, (mem_goodVertices _ v).mpr hgood, hv⟩
  · intro hx
    obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp hx
    exact ⟨v, hval, (mem_goodVertices
      (V := Vertex (n := n) t Q (realWeightedHash weights)) _ v).mp hv⟩
end DeletionCode.GoodWordBridge
