-- Prove2me | solution 1 for D1Bound5.coherent_cpow_half_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:05.653063+00:00
-- url     : https://prove2.me/submissions/1c49685d-2f12-4fb8-9b13-ef81accf51e0

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset Polynomial

namespace D1Bound5













end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5

/-- Squaring the principal half power recovers its argument, including
zero.  No change of logarithm branch is used. -/
theorem _root_.solution (z : ℂ) :
    (z ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = z := by
  simpa [one_div] using
    (Complex.cpow_nat_inv_pow z (n := 2) (by decide))







end D1Bound5
end
