-- Prove2me | solution 1 for CompactnessConjecture.symmetricQuadratic_char_two_eq_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/77a855db-4020-4494-91e5-2143d908c275

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricQuadratic_char_two

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K] [CharP K 2]
namespace CompactnessConjecture
theorem _root_.solution
    (r s b x y : K) :
    symmetricQuadratic (r ^ 2) b (s ^ 2) x y =
      (r * x + s * y) ^ 2 := by
  rw [symmetricQuadratic_char_two]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    r ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 =
        (r * x) ^ 2 + (s * y) ^ 2 := by ring
    _ = (r * x + s * y) ^ 2 := by
      rw [add_sq]
      simp [htwo]
end CompactnessConjecture
