-- Prove2me | solution 1 for CurveSymmetry.quadPlace_X_inv_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:45.842509+00:00
-- url     : https://prove2.me/submissions/5467d909-e769-4db9-b11b-a2e33318a32a

-- Solution generated from lean/QuadraticInfinity.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Theorems.Thm_CurveSymmetry_placeCenter_primeValuationSubring
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
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
section Generic
variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]
/-- An element of the center has no inverse in the valuation subring. -/
lemma inv_notMem_of_mem_placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O)
    {a : A} (ha : a ∈ placeCenter K O hO) (ha0 : algebraMap A K a ≠ 0) :
    (algebraMap A K a)⁻¹ ∉ O := by
  intro hinv
  rw [mem_placeCenter] at ha
  have h1 := (O.valuation_le_one_iff _).mpr hinv
  rw [map_inv₀] at h1
  have hpos : 0 < O.valuation (algebraMap A K a) := by
    rw [Valuation.pos_iff]
    exact ha0
  exact absurd ((inv_le_one₀ hpos).mp h1) (not_le.mpr ha)
end Generic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
    (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    (algebraMap ℂ[X] (QuadField h) X)⁻¹ ∈ quadPlace h c d hd ↔ c ≠ 0 := by
  have hA := algebraMap_mem_primeValuationSubring (K := QuadField h)
    (quadEval_ker_ne_bot h c d hd)
  have hcenter := placeCenter_primeValuationSubring (K := QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd)
  have hXeq : algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.of (quadPoly h) X) =
      algebraMap ℂ[X] (QuadField h) X :=
    ((quadRingMap h).commutes X)
  have hmem : AdjoinRoot.of (quadPoly h) X ∈ RingHom.ker (quadEval h c d hd) ↔ c = 0 := by
    rw [RingHom.mem_ker, quadEval_of, eval_X]
  have hX0 : algebraMap ℂ[X] (QuadField h) X ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h), RatFunc.algebraMap_X]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      RatFunc.X_ne_zero
  change (algebraMap ℂ[X] (QuadField h) X)⁻¹ ∈ primeValuationSubring (QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd) ↔ c ≠ 0
  rw [← hXeq]
  constructor
  · intro hinv hc
    have hin : AdjoinRoot.of (quadPoly h) X ∈ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_notMem_of_mem_placeCenter _ hA hin (hXeq ▸ hX0) hinv
  · intro hc
    have hnot : AdjoinRoot.of (quadPoly h) X ∉ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_mem_of_notMem_placeCenter _ hA hnot
end

#print axioms solution
