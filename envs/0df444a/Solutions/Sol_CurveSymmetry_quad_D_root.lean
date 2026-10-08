-- Prove2me | solution 1 for CurveSymmetry.quad_D_root
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:46.616195+00:00
-- url     : https://prove2.me/submissions/9244a4d8-d470-4abe-be95-5337595dfe90

-- Solution generated from lean/QuadraticDifferentials.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
import Theorems.Thm_CurveSymmetry_quad_D_algebraMap
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
theorem solution :
    (2 * AdjoinRoot.root (quadRat h)) •
        KaehlerDifferential.D ℂ (QuadField h) (AdjoinRoot.root (quadRat h)) =
      algebraMap ℂ[X] (QuadField h) h.derivative •
        KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  have hsq : AdjoinRoot.root (quadRat h) ^ 2 = algebraMap ℂ[X] (QuadField h) h := by
    rw [quadRoot_sq, ← IsScalarTower.algebraMap_apply]
  have hleft := (KaehlerDifferential.D ℂ (QuadField h)).leibniz_pow
    (a := AdjoinRoot.root (quadRat h)) 2
  rw [hsq, quad_D_algebraMap] at hleft
  rw [hleft]
  simp [pow_one, two_smul, two_mul, add_smul]
end

#print axioms solution
