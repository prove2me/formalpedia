-- Prove2me | solution 1 for D1Bound5.bennett_prod_erase_last_erase
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:00.776015+00:00
-- url     : https://prove2.me/submissions/a15815e6-f126-44de-bd9e-dcdecab2b84d

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



/-- The same reindexing with one further local pole omitted. -/
theorem _root_.solution {M : Type*} [CommMonoid M] (n : ℕ)
    (j : Fin n) (f : Fin (n + 1) → M) :
    (∏ l ∈ ((Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n)).erase
      j.castSucc, f l) = ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, f l.castSucc := by
  rw [← Finset.prod_ite_mem_eq, Fin.prod_univ_castSucc,
    ← Finset.prod_ite_mem_eq (Finset.univ.erase j)]
  simp





end D1Bound5
end
