-- Prove2me | solution 1 for CurveSymmetry.sixtyDegree_isometry_order
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:35.212445+00:00
-- url     : https://prove2.me/submissions/65acb227-259b-4b5b-a4ee-d9391dcf35d3

-- Solution generated from lean/QuinticExample.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
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
theorem sixtyDegree_primitive : IsPrimitiveRoot sixtyDegreeCoefficient 6 := by
  change IsPrimitiveRoot (Complex.exp ((Real.pi : ℂ) * Complex.I / 3)) 6
  convert Complex.isPrimitiveRoot_exp 6 (by decide) using 1
  congr 1
  norm_num
  ring
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution :
    orderOf (affineDirectIsometry sixtyDegreeCoefficient 0 sixtyDegree_norm) = 6 := by
  let f := affineDirectIsometry sixtyDegreeCoefficient 0 sixtyDegree_norm
  have hp : ∀ n : ℕ, ∀ z : ℂ, (f ^ n) z = sixtyDegreeCoefficient ^ n * z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ]
      change (f ^ n) (f z) = _
      rw [ih]
      simp [f, pow_succ, mul_assoc]
  have he : orderOf f = orderOf sixtyDegreeCoefficient := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    constructor
    · intro h
      have hz := congrArg (fun k : ℂ ≃ᵢ ℂ => k 1) h
      simpa [hp] using hz
    · intro h
      ext z
      simp [hp, h]
  exact he.trans sixtyDegree_primitive.eq_orderOf.symm
end

#print axioms solution
