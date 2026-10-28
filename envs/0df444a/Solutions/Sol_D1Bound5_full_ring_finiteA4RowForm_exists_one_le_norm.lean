-- Prove2me | solution 1 for D1Bound5.full_ring_finiteA4RowForm_exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:20:22.4848+00:00
-- url     : https://prove2.me/submissions/92818ee9-29d8-4837-b217-965c18b89fbb

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
import Definitions.Def_D1Bound5_FiniteA4IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteA4RowForm_exists_ne_zero
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem map_finiteA4Constant (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteA4Constant x y c i) = finiteA4Constant (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteA4Constant, map_ofNat]

@[simp] theorem map_finiteA4Left (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteA4Left x y c i) = finiteA4Left (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteA4Left, map_ofNat]

@[simp] theorem map_finiteA4Right (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteA4Right x y c i) = finiteA4Right (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteA4Right, map_ofNat]

@[simp] theorem map_finiteA4DividedMatrix (f : R →+* S)
    (x y c : R) (i j : Fin 3) :
    f (finiteA4DividedMatrix x y c i j) =
      finiteA4DividedMatrix (f x) (f y) (f c) i j := by
  fin_cases j <;> simp [finiteA4DividedMatrix]



@[simp] theorem map_finiteA4RowForm (f : R →+* S)
    (x y c z sX sY : R) (i : Fin 3) :
    f (finiteA4RowForm x y c z sX sY i) =
      finiteA4RowForm (f x) (f y) (f c) (f z) (f sX) (f sY) i := by
  simp only [finiteA4RowForm, Matrix.mulVec, dotProduct, map_sum, map_mul,
    map_finiteA4DividedMatrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  fin_cases j <;> rfl



/-- One actual A4 integer row has modulus at least one. Both integrality
and nonvanishing are obtained from the displayed polynomial construction. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (x y c z sX sY : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, 1 ≤ ‖finiteA4RowForm (phi (x : K)) (phi (y : K))
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
  obtain ⟨i, hi⟩ := finiteA4RowForm_exists_ne_zero
    (f x) (f y) (f c) (f z) (f sX) (f sY) (hnonzero x hx) (hnonzero y hy) (hnonzero c hc) (fun h => hxy (hf h)) hz'
  let L := finiteA4RowForm x y c z sX sY i
  have hL : f L = finiteA4RowForm (f x) (f y) (f c) (f z) (f sX) (f sY) i :=
    map_finiteA4RowForm f _ _ _ _ _ _ i
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
