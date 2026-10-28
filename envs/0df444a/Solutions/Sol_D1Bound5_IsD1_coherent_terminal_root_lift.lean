-- Prove2me | solution 1 for D1Bound5.IsD1.coherent_terminal_root_lift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:34.793786+00:00
-- url     : https://prove2.me/submissions/cfc40612-1909-4724-992d-16d9d02c3e5d

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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_complex_square_root_lift

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5







/-- The coherent terminal root of two actual tuple entries lifts to the
original ring, even though the auxiliary square root `eta` need not do so. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ) (hf : Function.Injective f)
    {T : Finset R} (hT : IsD1 T) {p q : R}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = f p * f q) :
    ∃ z : R, f z = coherentTerminalRoot (f p) (f q) eta := by
  have hp0 : f p ≠ 0 := by
    intro h
    exact hT.1 p hp (hf (by simpa only [map_zero] using h))
  have hq0 : f q ≠ 0 := by
    intro h
    exact hT.1 q hq (hf (by simpa only [map_zero] using h))
  obtain ⟨r, hr⟩ := hT.2 p hp q hq hpq
  have hr' : (f r) ^ 2 = f p * f q + 1 := by
    simpa only [pow_two, map_mul, map_add, map_one] using congrArg f hr
  apply complex_square_root_lift f _ r
  rw [hr']
  exact coherent_analytic_terminal_root_sq (f p) (f q) eta hp0 hq0 heta







end D1Bound5
end
