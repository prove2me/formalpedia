-- Prove2me | solution 1 for CompactnessConjecture.symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/944db8ac-43de-442f-9e23-a57a53daefae

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricQuadratic_char_two_eq_square
import Theorems.Thm_CompactnessConjecture_square_surjective_char_two

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K] [CharP K 2]
namespace CompactnessConjecture
theorem _root_.solution
    [Finite K] {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : symmetricQuadratic a b c x y = 0)
    (hsecond : symmetricQuadratic a b c x' y' = 0) :
    a = 0 ∧ c = 0 := by
  obtain ⟨r, hr⟩ := square_surjective_char_two a
  obtain ⟨s, hs⟩ := square_surjective_char_two c
  change r ^ 2 = a at hr
  change s ^ 2 = c at hs
  have hlinfirst : r * x + s * y = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hfirst
  have hlinsecond : r * x' + s * y' = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hsecond
  have hrdet : (x * y' - x' * y) * r = 0 := by
    linear_combination y' * hlinfirst - y * hlinsecond
  have hsdet : (x * y' - x' * y) * s = 0 := by
    linear_combination x * hlinsecond - x' * hlinfirst
  have hrzero : r = 0 := (mul_eq_zero.mp hrdet).resolve_left hind
  have hszero : s = 0 := (mul_eq_zero.mp hsdet).resolve_left hind
  constructor
  · simpa [hrzero] using hr.symm
  · simpa [hszero] using hs.symm
end CompactnessConjecture
