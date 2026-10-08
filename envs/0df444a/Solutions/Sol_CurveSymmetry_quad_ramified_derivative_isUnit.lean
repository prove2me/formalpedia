-- Prove2me | solution 1 for CurveSymmetry.quad_ramified_derivative_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:26.967691+00:00
-- url     : https://prove2.me/submissions/1ec3ee47-8e1a-4182-bbc8-c0477e6c9c5d

-- Solution generated from lean/PlaceUniformizers.lean (curve-symmetry-lean): inlined helpers in
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

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
theorem solution (hc : h.eval c = 0) :
    IsUnit (algebraMap (QuadRing h) (quadLocalRing h c d hd)
      (algebraMap ℂ[X] (QuadRing h) h.derivative)) := by
  obtain ⟨k, hk, hkc⟩ := exists_factor_of_root h c hc
  have hderiv : h.derivative.eval c = k.eval c := by
    rw [hk, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp
  have hmem : algebraMap ℂ[X] (QuadRing h) h.derivative ∈
      (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_algebraMap, hderiv]
    exact hkc
  exact IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hmem⟩
end

#print axioms solution
