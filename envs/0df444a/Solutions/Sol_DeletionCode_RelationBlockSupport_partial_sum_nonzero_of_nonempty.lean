-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.partial_sum_nonzero_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:54.68584+00:00
-- url     : https://prove2.me/submissions/b823261d-ffb3-4e56-bc4c-3d7c4a9872ff

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
import Theorems.Thm_DeletionCode_RelationBlockSupport_partial_sum_nonzero

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I H : Type*} (G : I → H → ℚ)
    (hG : LinearIndependent ℚ G) (T : Finset I) (a : I → ℚ)
    (hT : T.Nonempty) (ha : ∀ i ∈ T, a i ≠ 0) :
    ∃ g, (∑ i ∈ T, a i * G i g) ≠ 0 := by
  obtain ⟨i, hi⟩ := hT
  exact partial_sum_nonzero G hG T a ⟨i, hi, ha i hi⟩
end DeletionCode.RelationBlockSupport
