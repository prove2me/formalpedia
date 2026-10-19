-- Prove2me | solution 1 for CompactnessConjecture.symmetricQuadratic_eq_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/1db367ac-e54a-4524-a98e-9de6e6281e89

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [CommRing K]
namespace CompactnessConjecture
theorem _root_.solution
    (a b c x y : K) :
    symmetricQuadratic a b c x y =
      x * (a * x + b * y) + y * (b * x + c * y) := by
  unfold symmetricQuadratic
  ring
end CompactnessConjecture
