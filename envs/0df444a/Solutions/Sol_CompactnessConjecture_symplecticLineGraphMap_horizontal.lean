-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineGraphMap_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/8d6c30cc-2e34-4721-96c8-d30e993b061b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (x : L.1) :
    symplecticLineGraphMap K L hvertical
        (symplecticHorizontalProjection K
          (x : SymplecticVector K)) =
      symplecticVerticalProjection K
        (x : SymplecticVector K) := by
  change
    symplecticVerticalProjection K
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm
        (symplecticLineHorizontalProjectionEquiv K L hvertical x) :
          SymplecticVector K) = _
  rw [LinearEquiv.symm_apply_apply]
end CompactnessConjecture
