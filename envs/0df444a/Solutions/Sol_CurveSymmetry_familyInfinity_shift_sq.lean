-- Prove2me | solution 1 for CurveSymmetry.familyInfinity_shift_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:35.25672+00:00
-- url     : https://prove2.me/submissions/b897fffd-e26b-4065-9675-b2dc9d544d2a

-- Solution generated from lean/InfinityRegularity.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X])
lemma algebraMap_quadRing_apply (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y = quadRingMap h y := rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
lemma quadRing_root_sq : AdjoinRoot.root (quadPoly h) ^ 2 = algebraMap ℂ[X] (QuadRing h) h := by
  have := AdjoinRoot.eval₂_root (quadPoly h)
  rw [eval₂_quadPoly] at this
  rw [AdjoinRoot.algebraMap_eq]
  linear_combination this
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
omit [Fact (Irreducible (quadRat h))] in
/-- At a ramified point place, `(t − c)·k = w²` with `k(c) ≠ 0`: the coordinate `t − c`
is the square of the uniformizer up to a unit. -/
lemma quad_ramified_shift_sq (hc : h.eval c = 0) :
    ∃ k : ℂ[X], k.eval c ≠ 0 ∧
      quadShift h c * algebraMap ℂ[X] (QuadRing h) k = AdjoinRoot.root (quadPoly h) ^ 2 := by
  obtain ⟨k, hk, hkc⟩ := exists_factor_of_root h c hc
  refine ⟨k, hkc, ?_⟩
  rw [quadShift, ← map_mul, ← hk, quadRing_root_sq]
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    ∃ k : ℂ[X], k.eval 0 ≠ 0 ∧
      quadT (familyH m (star α)) * algebraMap ℂ[X] (QuadField (familyH m (star α))) k =
        AdjoinRoot.root (quadRat (familyH m (star α))) ^ 2 := by
  obtain ⟨k, hk0, hks⟩ := quad_ramified_shift_sq (familyH m (star α)) 0
    (familyH_eval_zero m (star α))
  refine ⟨k, hk0, ?_⟩
  set h' := familyH m (star α)
  have hmap := congrArg (algebraMap (QuadRing h') (QuadField h')) hks
  rw [map_mul, map_pow] at hmap
  have h1 : algebraMap (QuadRing h') (QuadField h') (quadShift h' 0) = quadT h' := by
    rw [quadShift, ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h'),
      C_0, sub_zero]
    rfl
  have h2 : algebraMap (QuadRing h') (QuadField h') (algebraMap ℂ[X] (QuadRing h') k) =
      algebraMap ℂ[X] (QuadField h') k :=
    (IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h') k).symm
  have h3 : algebraMap (QuadRing h') (QuadField h') (AdjoinRoot.root (quadPoly h')) =
      AdjoinRoot.root (quadRat h') := by
    rw [algebraMap_quadRing_apply, quadRingMap_root]
  rw [h1, h2, h3] at hmap
  exact hmap
end

#print axioms solution
