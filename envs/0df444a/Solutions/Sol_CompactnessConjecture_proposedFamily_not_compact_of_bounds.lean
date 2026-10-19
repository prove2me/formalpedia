-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_not_compact_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/78fd00da-cba1-4f1b-84ea-917f767ac269

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_manuscriptLowerConstant_pos
import Theorems.Thm_CompactnessConjecture_not_compact_of_separation

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology
namespace CompactnessConjecture
theorem _root_.solution
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ IsCompactFamily proposedFamily := by
  apply not_compact_of_separation
  exact
    { lowerConstant := manuscriptLowerConstant
      lowerConstant_pos := manuscriptLowerConstant_pos
      family_littleO := hupper
      member_lower := hlower }
end CompactnessConjecture
