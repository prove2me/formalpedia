-- Prove2me | solution 1 for DeletionCode.FiniteRelationBlocks.selected_block_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:27:47.090184+00:00
-- url     : https://prove2.me/submissions/169ad68a-c309-4b22-a60a-b27aaca198f6

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_selected_block_nonzero
import Theorems.Thm_DeletionCode_BlockPartition_incident_iff_rule
import Theorems.Thm_DeletionCode_GeneratingBlocks_nonzero_incident


set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators
namespace DeletionCode.FiniteRelationBlocks
theorem _root_.solution {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (B : RuleSet k) (hB : B ∈ selectedBlocks G I) :
    ∃ v, Incident B v ∧ Incident {w} v := by
  obtain ⟨g, u, hu, hug, hwg⟩ := selected_block_nonzero G I hIG w a hind ha hrel B hB
  exact ⟨gramPrefix g,
    (incident_iff_rule B (gramPrefix g)).mpr
      ⟨u, hu, GeneratingBlocks.nonzero_incident u g hug⟩,
    GeneratingBlocks.nonzero_incident w g hwg⟩
end DeletionCode.FiniteRelationBlocks
