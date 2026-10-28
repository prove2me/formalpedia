-- Prove2me | solution 1 for D1Bound5.full_ring_finiteMRowForm_exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:18:08.180364+00:00
-- url     : https://prove2.me/submissions/a366430c-d412-4910-8cc0-5b7af11fd30f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Theorems.Thm_D1Bound5_finiteMRowForm_exists_ne_zero
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
namespace D1Bound5























@[simp] theorem map_finiteMTermEval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : FiniteMTerm) (a b s v : R) :
    f (finiteMTermEval t a b s v) = finiteMTermEval t (f a) (f b) (f s) (f v) := by
  simp [finiteMTermEval]

@[simp] theorem map_finiteMDividedMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b s c : R) (i j : Fin 4) :
    f (finiteMDividedMatrix a b s c i j) =
      finiteMDividedMatrix (f a) (f b) (f s) (f c) i j := by
  have hv : f (![c,a*c+1,b*c+1,s*c+1] j) =
      ![f c,f a*f c+1,f b*f c+1,f s*f c+1] j := by
    fin_cases j <;> simp
  simp only [finiteMDividedMatrix, Matrix.of_apply, map_list_sum,
    List.map_map, Function.comp_def, map_finiteMTermEval, hv]


end D1Bound5
end
section
open scoped NumberField
open Module

namespace D1Bound5



@[simp] theorem map_finiteMRowForm {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b s c z rA rB rS : R) (i : Fin 4) :
    f (finiteMRowForm a b s c z rA rB rS i) =
      finiteMRowForm (f a) (f b) (f s) (f c) (f z) (f rA) (f rB) (f rS) i := by
  simp only [finiteMRowForm,Matrix.mulVec,dotProduct,map_sum,map_mul,map_finiteMDividedMatrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  fin_cases j <;> rfl



/-- An actual integral M row is nonzero because the proved divided
matrix determinant is nonzero. Arbitrary signed root products are
allowed, provided the terminal root is nonzero. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b s c z rA rB rS : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (hz : z ≠ 0) :
    ∃ i : Fin 4, 1 ≤ ‖finiteMRowForm (phi (a : K)) (phi (b : K)) (phi (s : K))
      (phi (c : K)) (phi (z : K)) (phi (rA : K)) (phi (rB : K)) (phi (rS : K)) i‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hn (x : 𝓞 K) (hx : x ≠ 0) : f x ≠ 0 := by
    intro h
    apply hx
    apply hf
    simpa only [map_zero] using h
  obtain ⟨i,hi⟩ := finiteMRowForm_exists_ne_zero
    (f a) (f b) (f s) (f c) (f z) (f rA) (f rB) (f rS)
    (hn a ha) (hn b hb) (hn s hs) (fun h => hab (hf h))
    (fun h => has (hf h)) (fun h => hbs (hf h)) (hn z hz)
  let L := finiteMRowForm a b s c z rA rB rS i
  have hL : f L = finiteMRowForm (f a) (f b) (f s) (f c) (f z) (f rA) (f rB) (f rS) i :=
    map_finiteMRowForm f _ _ _ _ _ _ _ _ i
  have hL0 : L ≠ 0 := by
    intro hzero
    apply hi
    rw [← hL,hzero,map_zero]
  have hbnd := one_le_norm_integer hK phi hL0
  change 1 ≤ ‖f L‖ at hbnd
  rw [hL] at hbnd
  exact ⟨i,hbnd⟩

end D1Bound5
end

