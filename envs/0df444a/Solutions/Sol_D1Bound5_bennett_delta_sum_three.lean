-- Prove2me | solution 1 for D1Bound5.bennett_delta_sum_three
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:07:56.625757+00:00
-- url     : https://prove2.me/submissions/70c92202-7e51-47f2-82de-2ecc35a1e118

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]







theorem _root_.solution (i : Fin 3) :
    (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) +
      (if i = 2 then 1 else 0) = (1 : ℕ) := by
  have h : (∑ j : Fin 3, if i = j then 1 else 0) = (1 : ℕ) := by simp
  simpa only [Fin.sum_univ_three] using h





















end D1Bound5
end
