-- Prove2me | solution 1 for D1Bound5.bennettTwoRowForm_lift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:35.908127+00:00
-- url     : https://prove2.me/submissions/92801f49-926b-4340-b403-9317dcf602dc

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_row_lift

section
open scoped NumberField
open Module

namespace D1Bound5





/-- The selected row is the image of an explicitly constructed ring
element. This uses the proved column divisibilities at every positive
order, including k=1. -/
theorem _root_.solution
    {R F : Type*} [CommRing R] [Field F] [CharZero F]
    (f : R →+* F) (a b c z sA sB : R)
    (ha : f a ≠ 0) (hb : f b ≠ 0) (hab : f a ≠ f b)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ L : R, f L = bennettTwoRowForm (f a) (f b) (f c) (f z) (f sA) (f sB) k i := by
  obtain ⟨q0, q1, q2, h0, h1, h2⟩ :=
    bennettTwoClearedEntry_row_lift f a b c ha hb hab k hk i
  refine ⟨q0*z + a^(k-1)*q1*sA + b^(k-1)*q2*sB, ?_⟩
  have hpow (x : F) : x^k = x^(k-1)*x := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  unfold bennettTwoRowForm
  rw [← h0, ← h1, ← h2]
  simp only [map_add, map_mul, map_pow]
  rw [hpow (f a), hpow (f b)]
  field_simp [ha, hb]
  <;> ring



end D1Bound5
end
