-- Prove2me | solution 1 for D1Bound5.full_ring_bennettTwoRowForm_exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:42:27.989755+00:00
-- url     : https://prove2.me/submissions/8e2ee85e-bdb4-4091-8b5a-f9f7212faa63

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions
import Theorems.Thm_D1Bound5_bennettTwoRowForm_exists_ne_zero
import Theorems.Thm_D1Bound5_bennettTwoRowForm_lift
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5







/-- In the full ring of integers of an imaginary quadratic field, an
actual Bennett row has modulus at least one. The determinant and
integrality are both derived from the constructed entries. The root
arguments can be any signed integral lifts obtained from the tuple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b c z sA sB : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hz : z ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    ∃ i : Fin 3, 1 ≤ ‖bennettTwoRowForm (phi (a : K)) (phi (b : K))
      (phi (c : K)) (phi (z : K)) (phi (sA : K)) (phi (sB : K)) k i‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hnonzero (x : 𝓞 K) (hx : x ≠ 0) : f x ≠ 0 := by
    intro h
    apply hx
    apply hf
    simpa only [map_zero] using h
  have hab' : f a ≠ f b := fun h => hab (hf h)
  obtain ⟨i, hi⟩ := bennettTwoRowForm_exists_ne_zero
    (f a) (f b) (f c) (f z) (f sA) (f sB)
    (hnonzero a ha) (hnonzero b hb) hab' (hnonzero z hz) k hk
  obtain ⟨L, hL⟩ := bennettTwoRowForm_lift f a b c z sA sB
    (hnonzero a ha) (hnonzero b hb) hab' k hk i
  have hL0 : L ≠ 0 := by
    intro hzero
    apply hi
    rw [← hL, hzero, map_zero]
  have hbound := one_le_norm_integer hK phi hL0
  change 1 ≤ ‖f L‖ at hbound
  rw [hL] at hbound
  exact ⟨i, hbound⟩

end D1Bound5
end
