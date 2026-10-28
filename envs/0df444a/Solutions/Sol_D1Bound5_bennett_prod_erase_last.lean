-- Prove2me | solution 1 for D1Bound5.bennett_prod_erase_last
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:05.822244+00:00
-- url     : https://prove2.me/submissions/54fffa98-ae3e-4c4d-8351-ef0f66e75a32

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- Products over all nodes except the last are products over the prefix. -/
theorem _root_.solution {M : Type*} [CommMonoid M] (n : ℕ)
    (f : Fin (n + 1) → M) :
    (∏ l ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n), f l) =
      ∏ l : Fin n, f l.castSucc := by
  rw [← Finset.prod_ite_mem_eq]
  rw [Fin.prod_univ_castSucc]
  simp







end D1Bound5
end
