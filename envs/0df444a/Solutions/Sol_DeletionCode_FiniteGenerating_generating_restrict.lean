-- Prove2me | solution 1 for DeletionCode.FiniteGenerating.generating_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:34.925248+00:00
-- url     : https://prove2.me/submissions/15d71cd4-7d5e-47ab-ac06-b871c03d9a90

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_GeneratingBlocks_nonzero_incident


set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition
namespace DeletionCode.FiniteGenerating
theorem _root_.solution {k : ℕ} (v : Gram (windowLength k) → ℤ)
    (G U : RuleSet k) (rank : (Gram (windowLength k) → ℤ) → ℕ)
    (hUG : U ⊆ G) (hclosed : ClosedIn G U) (hgen : GeneratingOn v G rank) :
    GeneratingOn v U rank := by
  intro u hu g hneg
  rcases hgen u (hUG hu) g hneg with hv | ⟨z, hz, hrank, hzg⟩
  · exact Or.inl hv
  · have hconnect : ConnectedIn G u z := Relation.EqvGen.rel _ _
      ⟨hUG hu, hz, gramPrefix g,
        GeneratingBlocks.nonzero_incident u g (by omega),
        GeneratingBlocks.nonzero_incident z g hzg⟩
    exact Or.inr ⟨z, hclosed u hu z hz hconnect, hrank, hzg⟩
end DeletionCode.FiniteGenerating
