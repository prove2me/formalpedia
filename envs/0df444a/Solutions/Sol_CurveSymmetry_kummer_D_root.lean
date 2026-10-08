-- Prove2me | solution 1 for CurveSymmetry.kummer_D_root
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:10.019563+00:00
-- url     : https://prove2.me/submissions/c5e50ec3-c2ad-4091-bfe4-c4153cbdd15e

-- Solution generated from lean/KummerField.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_10_KummerField
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
open Polynomial
section Field
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]
/-- The chain rule along `ℂ[x] → K`. -/
theorem kummer_D_algebraMap (p : ℂ[X]) :
    KaehlerDifferential.D ℂ (KummerField n f) (algebraMap ℂ[X] (KummerField n f) p) =
      algebraMap ℂ[X] (KummerField n f) p.derivative •
        KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  have hae : ∀ q : ℂ[X], aeval (kummerX n f) q = algebraMap ℂ[X] (KummerField n f) q := by
    intro q
    rw [kummerX, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [← hae p, (KaehlerDifferential.D ℂ (KummerField n f)).map_aeval p (kummerX n f), hae]
end Field
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]
theorem solution :
    ((n : KummerField n f) * AdjoinRoot.root (kummerRat n f) ^ (n - 1)) •
        KaehlerDifferential.D ℂ (KummerField n f) (AdjoinRoot.root (kummerRat n f)) =
      algebraMap ℂ[X] (KummerField n f) f.derivative •
        KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  have hpow := (KaehlerDifferential.D ℂ (KummerField n f)).leibniz_pow
    (a := AdjoinRoot.root (kummerRat n f)) n
  rw [kummerRoot_pow, kummer_D_algebraMap] at hpow
  rw [hpow, ← smul_smul, ← Nat.cast_smul_eq_nsmul (KummerField n f)]
end

#print axioms solution
