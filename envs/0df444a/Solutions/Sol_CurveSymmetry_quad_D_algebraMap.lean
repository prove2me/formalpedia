-- Prove2me | solution 1 for CurveSymmetry.quad_D_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:23.552228+00:00
-- url     : https://prove2.me/submissions/c6548679-52e5-4a78-ae97-941002338fb9

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

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
theorem solution (p : ℂ[X]) :
    KaehlerDifferential.D ℂ (QuadField h) (algebraMap ℂ[X] (QuadField h) p) =
      algebraMap ℂ[X] (QuadField h) p.derivative •
        KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  have hae : ∀ q : ℂ[X], aeval (quadT h) q = algebraMap ℂ[X] (QuadField h) q := by
    intro q
    rw [quadT, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [← hae p, (KaehlerDifferential.D ℂ (QuadField h)).map_aeval p (quadT h), hae]
end

#print axioms solution
