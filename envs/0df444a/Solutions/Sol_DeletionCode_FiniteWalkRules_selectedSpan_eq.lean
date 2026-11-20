-- Prove2me | solution 1 for DeletionCode.FiniteWalkRules.selectedSpan_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:44:03.399477+00:00
-- url     : https://prove2.me/submissions/8014cfbc-eeaf-4874-8657-7ca509f8d53b

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_image_selectedRules

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}
namespace DeletionCode.FiniteWalkRules
theorem _root_.solution
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    selectedSpan (walkStep (rationalPath p)) S =
      Submodule.span ℚ (rational '' (↑(selectedRules p S) : Set _)) := by
  rw [rational_image_selectedRules]
  rfl
end DeletionCode.FiniteWalkRules
