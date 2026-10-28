-- Prove2me | solution 1 for D1Bound5.complex_square_root_lift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:50:26.076282+00:00
-- url     : https://prove2.me/submissions/4344fddf-a9cb-4c53-9298-6702d69af5da

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5





/-- A complex number whose square agrees with that of a ring element
already lies in the image of that ring.  Zero roots are permitted. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ) (z : ℂ) (r : R)
    (h : z ^ 2 = (f r) ^ 2) : ∃ t : R, f t = z := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨r, h.symm⟩
  · exact ⟨-r, by simpa only [map_neg] using h.symm⟩









end D1Bound5
end
