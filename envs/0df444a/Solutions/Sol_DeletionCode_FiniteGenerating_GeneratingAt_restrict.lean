-- Prove2me | solution 1 for DeletionCode.FiniteGenerating.GeneratingAt.restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:52.602187+00:00
-- url     : https://prove2.me/submissions/e879801f-95db-4714-ae30-074c5103bc65

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_FiniteGenerating_independent_restrict
import Theorems.Thm_DeletionCode_FiniteGenerating_generating_restrict
import Theorems.Thm_DeletionCode_GeneratingBlocks_generating_restrict


set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition
namespace DeletionCode.FiniteGenerating
namespace GeneratingAt
theorem _root_.solution {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G U : RuleSet k} (hgen : GeneratingAt v G) (hUG : U ⊆ G)
    (hclosed : ClosedIn G U) : GeneratingAt v U := by
  obtain ⟨rank, hinj, horder⟩ := hgen.ordered
  refine ⟨independent_restrict hUG hgen.independent, rank, ?_,
    generating_restrict v G U rank hUG hclosed horder⟩
  intro a ha b hb hab
  exact hinj (hUG ha) (hUG hb) hab
end GeneratingAt
end DeletionCode.FiniteGenerating
