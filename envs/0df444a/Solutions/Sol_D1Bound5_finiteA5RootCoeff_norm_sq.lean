-- Prove2me | solution 1 for D1Bound5.finiteA5RootCoeff_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:11.673666+00:00
-- url     : https://prove2.me/submissions/90449f3a-9711-43c4-81b7-3d8bec19ecd3

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_finiteFixedHomogeneous_map
import Theorems.Thm_D1Bound5_finiteFixedHomogeneous_neg
import Theorems.Thm_D1Bound5_finiteFixedHomogeneous_star
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





theorem finiteA5RootCoeff_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x y : R) (i : Fin 3) (j : Fin 2) (ell : Fin 6) :
    f (finiteA5RootCoeff x y i j ell) = finiteA5RootCoeff (f x) (f y) i j ell := by
  fin_cases ell <;> simp [finiteA5RootCoeff,finiteFixedHomogeneous_map]

theorem finiteA5RootCoeff_symmetry_norm {tau nu : ℤ}
    (sgn conj : Bool) (x y : QuadInt tau nu) (i : Fin 3) (j : Fin 2) (ell : Fin 6) :
    (finiteA5RootCoeff (smallExtensionSymmetry sgn conj x)
      (smallExtensionSymmetry sgn conj y) i j ell).norm =
      (finiteA5RootCoeff x y i j ell).norm := by
  cases sgn <;> cases conj <;> fin_cases ell
  all_goals
    simp [smallExtensionSymmetry,finiteA5RootCoeff,finiteFixedHomogeneous_neg,
      finiteFixedHomogeneous_star,QuadraticAlgebra.norm_star,QuadraticAlgebra.norm_neg]

theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (phi : K →+* ℂ) {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (sgn conj : Bool) (x y : 𝓞 K) (i : Fin 3) (j : Fin 2) (ell : Fin 6) :
    ‖finiteA5RootCoeff (phi (x : K)) (phi (y : K)) i j ell‖^2 =
      ((finiteA5RootCoeff
        (smallExtensionSymmetry sgn conj (e.symm x))
        (smallExtensionSymmetry sgn conj (e.symm y)) i j ell).norm : ℝ) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have h := norm_sq_full_ring_equiv e phi
    (finiteA5RootCoeff (e.symm x) (e.symm y) i j ell)
  have he : e (finiteA5RootCoeff (e.symm x) (e.symm y) i j ell) =
      finiteA5RootCoeff x y i j ell := by
    have he' := finiteA5RootCoeff_map e.toRingHom (e.symm x) (e.symm y) i j ell
    change e (finiteA5RootCoeff (e.symm x) (e.symm y) i j ell) =
      finiteA5RootCoeff (e (e.symm x)) (e (e.symm y)) i j ell at he'
    simpa only [RingEquiv.apply_symm_apply] using he'
  have hf := finiteA5RootCoeff_map f x y i j ell
  have hnorm : ‖finiteA5RootCoeff (f x) (f y) i j ell‖^2 =
      ((finiteA5RootCoeff (e.symm x) (e.symm y) i j ell).norm : ℝ) := by
    rw [←hf]
    change ‖phi ((finiteA5RootCoeff x y i j ell : 𝓞 K) : K)‖^2 =
      ((finiteA5RootCoeff (e.symm x) (e.symm y) i j ell).norm : ℝ)
    simpa only [he] using h
  rw [finiteA5RootCoeff_symmetry_norm]
  exact hnorm





end D1Bound5
end
