-- Prove2me | solution 1 for CurveSymmetry.quadLocal_poly_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:22.008835+00:00
-- url     : https://prove2.me/submissions/b62cd9ae-9dcd-4299-8798-bc5eea5f58c8

-- Solution generated from lean/HolomorphicDifferentials.lean (curve-symmetry-lean): inlined helpers in
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
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
lemma quadEval_algebraMap (p : ℂ[X]) :
    quadEval h c d hd (algebraMap ℂ[X] (QuadRing h) p) = p.eval c := by
  rw [AdjoinRoot.algebraMap_eq, quadEval_of]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- An element that becomes a unit of the local ring has its inverse there. -/
lemma quadLocal_inv_mem_of_isUnit {x : QuadRing h}
    (hx : IsUnit (algebraMap (QuadRing h) (quadLocalRing h c d hd) x)) :
    (algebraMap (QuadRing h) (QuadField h) x)⁻¹ ∈ quadLocalRing h c d hd := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hcoe : algebraMap (QuadRing h) (QuadField h) x * (y : QuadField h) = 1 := by
    have hc1 := congrArg (fun z : quadLocalRing h c d hd => (z : QuadField h)) hy
    simpa using hc1
  rw [inv_eq_of_mul_eq_one_right hcoe]
  exact y.2
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
theorem solution (p : ℂ[X]) (hp : p.eval c ≠ 0) :
    algebraMap ℂ[X] (QuadField h) p ∈ quadLocalRing h c d hd ∧
      (algebraMap ℂ[X] (QuadField h) p)⁻¹ ∈ quadLocalRing h c d hd := by
  have htower : algebraMap ℂ[X] (QuadField h) p =
      algebraMap (QuadRing h) (QuadField h) (algebraMap ℂ[X] (QuadRing h) p) := by
    rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
  have hmem : algebraMap ℂ[X] (QuadRing h) p ∈ (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_algebraMap]
    exact hp
  refine ⟨?_, ?_⟩
  · rw [htower]
    exact Subalgebra.algebraMap_mem _ _
  · rw [htower]
    exact quadLocal_inv_mem_of_isUnit h c d hd
      (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hmem⟩)
end

#print axioms solution
