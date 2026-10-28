-- Prove2me | solution 1 for D1Bound5.IsD1.coherent_linear_form_lift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:25:42.448598+00:00
-- url     : https://prove2.me/submissions/b71cfb6d-7bdb-49bd-8d60-c2c51fcb098c

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
import Theorems.Thm_D1Bound5_IsD1_coherent_anchor_root_lift
import Theorems.Thm_D1Bound5_IsD1_coherent_terminal_root_lift

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5











/-- Any polynomial-weighted coherent linear form on actual tuple roots
lifts to the original ring.  This supplies the arithmetic bridge after
the explicit Vandermonde quotient weights have been simplified. -/
theorem _root_.solution
    {R ι : Type*} [CommRing R] [Fintype ι]
    (f : R →+* ℂ) (hf : Function.Injective f)
    {T : Finset R} (hT : IsD1 T) {p q : R}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (a c : ι → R) (Delta : R)
    (ha : ∀ i, a i ∈ T) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = f p * f q) :
    ∃ L : R, f L =
      -f Delta * coherentTerminalRoot (f p) (f q) eta +
        ∑ i, f (c i) * coherentAnchorRoot (f (a i)) (f p) (f q) eta := by
  classical
  obtain ⟨z, hz⟩ := hT.coherent_terminal_root_lift f hf hp hq hpq eta heta
  choose r hr using fun i =>
    hT.coherent_anchor_root_lift f hf (ha i) hp hq (hap i) (haq i) eta heta
  refine ⟨-Delta * z + ∑ i, c i * r i, ?_⟩
  simp only [map_add, map_mul, map_neg, map_sum, hz, hr]



end D1Bound5
end
