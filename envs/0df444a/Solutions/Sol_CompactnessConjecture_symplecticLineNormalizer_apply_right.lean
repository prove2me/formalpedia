-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineNormalizer_apply_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/d749ae6b-e05e-462c-95a7-f42418991a43

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) :
    symplecticLineNormalizer K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    (0 : L.1) y
  simpa using h
end CompactnessConjecture
