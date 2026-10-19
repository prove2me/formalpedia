-- Prove2me | solution 1 for CompactnessConjecture.symmetricDet_zero_diagonal_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/0047a756-e505-411f-8747-0d40cec551dc

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [CommRing K]
namespace CompactnessConjecture
theorem _root_.solution (b b' : K) :
    symmetricDet (0 : K) (b - b') 0 = -((b - b') ^ 2) := by
  simp [symmetricDet]
end CompactnessConjecture
