-- Prove2me | solution 1 for D1Bound5.full_ring_finiteA3RowForm_exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:22:59.825429+00:00
-- url     : https://prove2.me/submissions/403d9e68-a69c-4f00-85f4-2084da9bf356

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_FiniteA3IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteA3RowForm_exists_ne_zero
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem map_finiteA3Constant (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteA3Constant x y c i) = finiteA3Constant (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteA3Constant, map_ofNat]

@[simp] theorem map_finiteA3Left (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteA3Left x y c i) = finiteA3Left (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteA3Left, map_ofNat]

@[simp] theorem map_finiteA3Right (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteA3Right x y c i) = finiteA3Right (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteA3Right, map_ofNat]

@[simp] theorem map_finiteA3DividedMatrix (f : R →+* S)
    (x y c : R) (i j : Fin 3) :
    f (finiteA3DividedMatrix x y c i j) =
      finiteA3DividedMatrix (f x) (f y) (f c) i j := by
  fin_cases j <;> simp [finiteA3DividedMatrix]



@[simp] theorem map_finiteA3RowForm (f : R →+* S)
    (x y c z sX sY : R) (i : Fin 3) :
    f (finiteA3RowForm x y c z sX sY i) =
      finiteA3RowForm (f x) (f y) (f c) (f z) (f sX) (f sY) i := by
  simp only [finiteA3RowForm, Matrix.mulVec, dotProduct, map_sum, map_mul,
    map_finiteA3DividedMatrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  fin_cases j <;> rfl



/-- One actual A3 integer row has modulus at least one. Both integrality
and nonvanishing are obtained from the displayed polynomial construction. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (x y c z sX sY : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, 1 ≤ ‖finiteA3RowForm (phi (x : K)) (phi (y : K))
      (phi (c : K)) (phi (z : K)) (phi (sX : K)) (phi (sY : K)) i‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro a b hab
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hab
  have hnonzero (a : 𝓞 K) (ha : a ≠ 0) : f a ≠ 0 := by
    intro h
    apply ha
    apply hf
    simpa only [map_zero] using h
  have hz' : f z ≠ 0 := by
    intro h
    apply hz
    apply hf
    simpa only [map_zero] using h
  obtain ⟨i, hi⟩ := finiteA3RowForm_exists_ne_zero
    (f x) (f y) (f c) (f z) (f sX) (f sY) (hnonzero x hx) (hnonzero y hy) (hnonzero c hc) (fun h => hxy (hf h)) hz'
  let L := finiteA3RowForm x y c z sX sY i
  have hL : f L = finiteA3RowForm (f x) (f y) (f c) (f z) (f sX) (f sY) i :=
    map_finiteA3RowForm f _ _ _ _ _ _ i
  have hL0 : L ≠ 0 := by
    intro hzero
    apply hi
    rw [← hL, hzero, map_zero]
  have hbound := one_le_norm_integer hK phi hL0
  change 1 ≤ ‖f L‖ at hbound
  rw [hL] at hbound
  exact ⟨i,hbound⟩

end D1Bound5
end
