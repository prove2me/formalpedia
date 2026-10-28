-- Prove2me | solution 1 for D1Bound5.finiteN2FixedPolynomial_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:47.031214+00:00
-- url     : https://prove2.me/submissions/e60a8b6e-826f-4c1d-ae4f-d55f60b58a1f

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_finiteN2FixedPolynomial_symmetry_norm
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Homogeneous coefficient evaluation commutes with ring maps. -/
theorem finiteHomogeneousTwo_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (v : Fin (n+1) → ℤ) (x y : R) :
    f (finiteHomogeneousTwo n v x y) = finiteHomogeneousTwo n v (f x) (f y) := by
  simp [finiteHomogeneousTwo]





theorem finiteN2FixedPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x y : R) (i : Fin 3) (j : Fin 2) (ell : Fin 3) :
    f (finiteN2FixedPolynomial x y i j ell) =
      finiteN2FixedPolynomial (f x) (f y) i j ell := by
  fin_cases ell <;> simp [finiteN2FixedPolynomial,finiteHomogeneousTwo_map]



/-- The exact field norm of each evaluated coefficient is its squared
complex modulus, including half-integral full rings and all four
allowed normalization symmetries. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (phi : K →+* ℂ) {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (sgn conj : Bool) (x y : 𝓞 K) (i : Fin 3) (j : Fin 2) (ell : Fin 3) :
    ‖finiteN2FixedPolynomial (phi (x : K)) (phi (y : K)) i j ell‖^2 =
      ((finiteN2FixedPolynomial
        (smallExtensionSymmetry sgn conj (e.symm x))
        (smallExtensionSymmetry sgn conj (e.symm y)) i j ell).norm : ℝ) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have h := norm_sq_full_ring_equiv e phi
    (finiteN2FixedPolynomial (e.symm x) (e.symm y) i j ell)
  have he : e (finiteN2FixedPolynomial (e.symm x) (e.symm y) i j ell) =
      finiteN2FixedPolynomial x y i j ell := by
    have he' := finiteN2FixedPolynomial_map e.toRingHom (e.symm x) (e.symm y) i j ell
    change e (finiteN2FixedPolynomial (e.symm x) (e.symm y) i j ell) =
      finiteN2FixedPolynomial (e (e.symm x)) (e (e.symm y)) i j ell at he'
    simpa only [RingEquiv.apply_symm_apply] using he'
  have hf := finiteN2FixedPolynomial_map f x y i j ell
  have hnorm : ‖finiteN2FixedPolynomial (f x) (f y) i j ell‖^2 =
      ((finiteN2FixedPolynomial (e.symm x) (e.symm y) i j ell).norm : ℝ) := by
    rw [←hf]
    change ‖phi ((finiteN2FixedPolynomial x y i j ell : 𝓞 K) : K)‖^2 =
      ((finiteN2FixedPolynomial (e.symm x) (e.symm y) i j ell).norm : ℝ)
    simpa only [he] using h
  rw [finiteN2FixedPolynomial_symmetry_norm]
  exact hnorm





end D1Bound5
end
