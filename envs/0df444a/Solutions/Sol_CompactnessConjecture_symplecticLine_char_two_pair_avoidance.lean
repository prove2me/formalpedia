-- Prove2me | solution 1 for CompactnessConjecture.symplecticLine_char_two_pair_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/43e8a05b-59b4-4141-acb0-5983862a4de9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLine_char_two_disjoint_of_two_common_center_pairs

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K] [CharP K 2] [Finite K]
namespace CompactnessConjecture
theorem _root_.solution :
    CharTwoLinePairAvoidance K :=
  symplecticLine_char_two_disjoint_of_two_common_center_pairs K
end CompactnessConjecture
