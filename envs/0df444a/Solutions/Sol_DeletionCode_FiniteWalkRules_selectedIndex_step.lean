-- Prove2me | solution 1 for DeletionCode.FiniteWalkRules.selectedIndex_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:44:02.926324+00:00
-- url     : https://prove2.me/submissions/b429fc90-b14c-4f16-80c7-527d2f61faa2

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
import Theorems.Thm_DeletionCode_FiniteWalkRules_selected_step_injOn
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedIndex_spec

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}
namespace DeletionCode.FiniteWalkRules
theorem _root_.solution
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) :
    (selectedIndex p S ⟨step p i, step_mem_selectedRules p S i hi⟩).val = i :=
  selected_step_injOn p S hind (selectedIndex p S _).property hi
    (selectedIndex_spec p S _)
end DeletionCode.FiniteWalkRules
