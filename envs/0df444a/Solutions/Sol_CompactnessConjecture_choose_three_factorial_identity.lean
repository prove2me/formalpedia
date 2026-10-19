-- Prove2me | solution 1 for CompactnessConjecture.choose_three_factorial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/1e838963-b8ad-41ed-a025-bba42a9978ef

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution (t : ℕ) :
    6 * t.choose 3 = t * (t - 1) * (t - 2) := by
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using
    (Nat.descFactorial_eq_factorial_mul_choose t 3).symm
end CompactnessConjecture
