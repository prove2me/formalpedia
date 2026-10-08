-- Prove2me | solution 1 for CurveSymmetry.mixedProjectiveChart_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:15.32398+00:00
-- url     : https://prove2.me/submissions/49b4bd1a-a378-470e-9ec8-fa71da4713ab

-- Solution generated from lean/ProjectiveChartMaps.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem affineLinePoint_injective : Function.Injective affineLinePoint := by
  intro x y h
  change sphereProjectiveEquiv (x : Sphere) = sphereProjectiveEquiv (y : Sphere) at h
  exact OnePoint.coe_injective (sphereProjectiveEquiv.injective h)
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem reciprocalLinePoint_injective : Function.Injective reciprocalLinePoint := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
  simpa [h0] using h1.symm
end
end CurveSymmetry

section
open CurveSymmetry
open OnePoint
set_option autoImplicit false
theorem solution : Function.Injective mixedProjectiveChart := by
  intro v w h
  have h0 := reciprocalLinePoint_injective (congrArg Prod.fst h)
  have h1 := affineLinePoint_injective (congrArg Prod.snd h)
  ext i
  fin_cases i <;> assumption
end

#print axioms solution
