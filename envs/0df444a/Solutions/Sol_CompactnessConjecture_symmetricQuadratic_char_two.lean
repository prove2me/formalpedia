-- Prove2me | solution 1 for CompactnessConjecture.symmetricQuadratic_char_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/5f069f1f-b19f-4244-87aa-970cd9b02422

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K] [CharP K 2]
namespace CompactnessConjecture
theorem _root_.solution
    (a b c x y : K) :
    symmetricQuadratic a b c x y = a * x ^ 2 + c * y ^ 2 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [symmetricQuadratic, htwo]
end CompactnessConjecture
