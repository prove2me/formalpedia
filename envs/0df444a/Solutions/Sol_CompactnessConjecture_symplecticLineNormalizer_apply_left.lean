-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineNormalizer_apply_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/34992961-8629-4c6e-a984-3a7dd82de946

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
    (x : L.1) :
    symplecticLineNormalizer K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    x (0 : M.1)
  simpa [standardSymplecticForm] using h
end CompactnessConjecture
