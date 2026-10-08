-- Prove2me | solution 1 for CurveSymmetry.quad_kaehler_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:25.063637+00:00
-- url     : https://prove2.me/submissions/77e44e51-c818-43d6-a6e3-fa32ba2c9554

-- Solution generated from lean/QuadraticDifferentials.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
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
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section BaseChange
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T] {ι : Type*} [Unique ι]
omit [Unique ι] in
@[simp] lemma kaehlerBasisOfEtale_apply (b : Module.Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfEtale, Module.Basis.baseChange_apply,
    KaehlerDifferential.mapBaseChange_tmul]
end BaseChange
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma polynomialKaehlerBasis_apply (i : Unit) :
    polynomialKaehlerBasis i = KaehlerDifferential.D ℂ ℂ[X] X := by
  simp [polynomialKaehlerBasis, Module.Basis.singleton_apply,
    KaehlerDifferential.polynomialEquiv_symm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma ratFuncKaehlerBasis_apply (i : Unit) :
    ratFuncKaehlerBasis i = KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
  rw [ratFuncKaehlerBasis, kaehlerBasisOfEtale_apply, polynomialKaehlerBasis_apply,
    KaehlerDifferential.map_D, RatFunc.algebraMap_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
lemma quadT_eq : quadT h = algebraMap (RatFunc ℂ) (QuadField h) RatFunc.X := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h), RatFunc.algebraMap_X]
end Quad
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
@[simp] lemma quadKaehlerBasis_apply (i : Unit) :
    quadKaehlerBasis h i = KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  rw [quadKaehlerBasis, kaehlerBasisOfEtale_apply, ratFuncKaehlerBasis_apply,
    KaehlerDifferential.map_D, quadT_eq]
end Quad
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
theorem solution :
    Submodule.span (QuadField h) {KaehlerDifferential.D ℂ (QuadField h) (quadT h)} = ⊤ := by
  have hrange : Set.range (quadKaehlerBasis h) =
      {KaehlerDifferential.D ℂ (QuadField h) (quadT h)} := by
    rw [Set.range_unique, quadKaehlerBasis_apply]
  rw [← hrange]
  exact (quadKaehlerBasis h).span_eq
end

#print axioms solution
