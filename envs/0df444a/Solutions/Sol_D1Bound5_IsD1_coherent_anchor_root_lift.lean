-- Prove2me | solution 1 for D1Bound5.IsD1.coherent_anchor_root_lift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:44.599502+00:00
-- url     : https://prove2.me/submissions/b9f9f941-fd7b-4ae8-a6b7-6d760c458f36

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
import Theorems.Thm_D1Bound5_coherent_analytic_anchor_root_sq
import Theorems.Thm_D1Bound5_complex_square_root_lift

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5









/-- Every coherent analytic anchor root of actual tuple entries lifts
to their original ring.  The lift is a signed product of the two tuple
square roots; no assumption of a nonzero pair product is required. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ) (hf : Function.Injective f)
    {T : Finset R} (hT : IsD1 T) {a p q : R}
    (ha : a ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hap : a ≠ p) (haq : a ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = f p * f q) :
    ∃ r : R, f r = coherentAnchorRoot (f a) (f p) (f q) eta := by
  have hnonzero (u : R) (hu : u ∈ T) : f u ≠ 0 := by
    intro h
    exact hT.1 u hu (hf (by simpa only [map_zero] using h))
  obtain ⟨r, hr⟩ := hT.2 a ha p hp hap
  obtain ⟨t, ht⟩ := hT.2 a ha q hq haq
  have hr' : (f r) ^ 2 = f a * f p + 1 := by
    simpa only [pow_two, map_mul, map_add, map_one] using congrArg f hr
  have ht' : (f t) ^ 2 = f a * f q + 1 := by
    simpa only [pow_two, map_mul, map_add, map_one] using congrArg f ht
  apply complex_square_root_lift f _ (r * t)
  rw [map_mul, mul_pow, hr', ht']
  exact coherent_analytic_anchor_root_sq (f a) (f p) (f q) eta
    (hnonzero a ha) (hnonzero p hp) (hnonzero q hq) heta





end D1Bound5
end
