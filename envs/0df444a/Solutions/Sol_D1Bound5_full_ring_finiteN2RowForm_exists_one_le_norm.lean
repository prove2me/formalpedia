-- Prove2me | solution 1 for D1Bound5.full_ring_finiteN2RowForm_exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:04.470639+00:00
-- url     : https://prove2.me/submissions/f5bd56f6-27b7-4401-a91c-cf76b9883601

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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteN2RowForm_exists_ne_zero
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem map_finiteN2Constant (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteN2Constant x y c i) = finiteN2Constant (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteN2Constant, map_ofNat]

@[simp] theorem map_finiteN2Left (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteN2Left x y c i) = finiteN2Left (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteN2Left, map_ofNat]

@[simp] theorem map_finiteN2Right (f : R →+* S) (x y c : R) (i : Fin 3) :
    f (finiteN2Right x y c i) = finiteN2Right (f x) (f y) (f c) i := by
  fin_cases i <;> simp [finiteN2Right, map_ofNat]

@[simp] theorem map_finiteN2DividedMatrix (f : R →+* S)
    (x y c : R) (i j : Fin 3) :
    f (finiteN2DividedMatrix x y c i j) =
      finiteN2DividedMatrix (f x) (f y) (f c) i j := by
  fin_cases j <;> simp [finiteN2DividedMatrix]



@[simp] theorem map_finiteN2RowForm (f : R →+* S)
    (x y c z sX sY : R) (i : Fin 3) :
    f (finiteN2RowForm x y c z sX sY i) =
      finiteN2RowForm (f x) (f y) (f c) (f z) (f sX) (f sY) i := by
  simp only [finiteN2RowForm, Matrix.mulVec, dotProduct, map_sum, map_mul,
    map_finiteN2DividedMatrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  fin_cases j <;> rfl



/-- One actual N2 integer row has modulus at least one. Both integrality
and nonvanishing are obtained from the displayed polynomial construction. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (x y c z sX sY : 𝓞 K) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, 1 ≤ ‖finiteN2RowForm (phi (x : K)) (phi (y : K))
      (phi (c : K)) (phi (z : K)) (phi (sX : K)) (phi (sY : K)) i‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro a b hab
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hab
  have hz' : f z ≠ 0 := by
    intro h
    apply hz
    apply hf
    simpa only [map_zero] using h
  obtain ⟨i, hi⟩ := finiteN2RowForm_exists_ne_zero
    (f x) (f y) (f c) (f z) (f sX) (f sY) (fun h => hxy (hf h)) hz'
  let L := finiteN2RowForm x y c z sX sY i
  have hL : f L = finiteN2RowForm (f x) (f y) (f c) (f z) (f sX) (f sY) i :=
    map_finiteN2RowForm f _ _ _ _ _ _ i
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
