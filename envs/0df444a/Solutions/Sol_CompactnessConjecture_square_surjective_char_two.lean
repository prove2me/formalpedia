-- Prove2me | solution 1 for CompactnessConjecture.square_surjective_char_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/b6a6fc9b-99f4-429e-8478-e4b66965fd57

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K] [CharP K 2]
namespace CompactnessConjecture
theorem _root_.solution [Finite K] :
    Function.Surjective (fun x : K => x ^ 2) := by
  intro a
  obtain ⟨r, hr⟩ := (isSquare_of_charTwo' a).exists_sq
  exact ⟨r, hr.symm⟩
end CompactnessConjecture
