-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.connected_block_meets_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:38.771045+00:00
-- url     : https://prove2.me/submissions/099ba205-a1aa-455f-96d8-71025f4a61ac

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
import Theorems.Thm_DeletionCode_RelationBlockSupport_connected_block_nonzero
import Theorems.Thm_DeletionCode_GeneratingBlocks_nonzero_incident


set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (b : I)
    (hactive : ∃ i, Connected G b i ∧ a i ≠ 0) :
    ∃ i, Connected G b i ∧ ∃ v, Incident {G i} v ∧ Incident {w} v := by
  obtain ⟨g, i, hi, hgi, hw⟩ := connected_block_nonzero G w a hG hrel b hactive
  exact ⟨i, hi, gramPrefix g, nonzero_incident (G i) g hgi,
    nonzero_incident w g hw⟩
end DeletionCode.RelationBlockSupport
