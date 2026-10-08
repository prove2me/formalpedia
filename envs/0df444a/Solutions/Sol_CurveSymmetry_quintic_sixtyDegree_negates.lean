-- Prove2me | solution 1 for CurveSymmetry.quintic_sixtyDegree_negates
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:50.932987+00:00
-- url     : https://prove2.me/submissions/988651d2-68c5-4231-8199-1bb0f187855e

-- Solution generated from lean/QuinticExample.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_quinticValue_eq
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
theorem sixtyDegree_cube : sixtyDegreeCoefficient ^ 3 = -1 := by
  rw [sixtyDegreeCoefficient, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (3 : ℂ) * ((Real.pi : ℂ) * Complex.I / 3) = Real.pi * Complex.I := by ring
  rw [he, Complex.exp_pi_mul_I]
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution (z : ℂ) :
    quinticValue (sixtyDegreeCoefficient * z) = -quinticValue z := by
  rw [quinticValue_eq, quinticValue_eq, mul_pow, sixtyDegree_cube,
    norm_mul, sixtyDegree_norm, one_mul]
  simp
end

#print axioms solution
