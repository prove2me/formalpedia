-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.nonzero_incident
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:09:29.639653+00:00
-- url     : https://prove2.me/submissions/14fc4f0b-32f0-4878-8a4b-775fc9421417

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {L : ℕ} (w : Gram L → ℤ) (g : Gram L) (hg : w g ≠ 0) :
    Incident {w} (gramPrefix g) := by
  classical
  exact ⟨gramSuffix g, Or.inl ⟨w, by simp, g, hg, rfl, rfl⟩⟩
end DeletionCode.GeneratingBlocks
