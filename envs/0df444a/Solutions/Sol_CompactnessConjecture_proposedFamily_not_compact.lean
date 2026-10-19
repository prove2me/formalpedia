-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_not_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/a7c0667a-4ab1-446c-bc8f-330494c30c94

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_not_compact_of_bounds
import Theorems.Thm_CompactnessConjecture_proposedFamily_familyLittleO
import Theorems.Thm_CompactnessConjecture_proposedFamily_uniformMemberLower

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution :
    ¬ IsCompactFamily proposedFamily :=
  proposedFamily_not_compact_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower
end CompactnessConjecture
