-- Prove2me | solution 1 for CurveSymmetry.mobius_antidiagonal_action
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:16.094555+00:00
-- url     : https://prove2.me/submissions/712ad1eb-ceea-4625-931d-d627cc94e465

-- Solution generated from lean/MobiusPair.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_finite_formula (g : MobiusMatrix) (z : ℂ) :
    g • (z : Sphere) = if g 1 0 * z + g 1 1 = 0 then ∞
      else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) :=
  OnePoint.smul_some_eq_ite
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_infinity_formula (g : MobiusMatrix) :
    g • (∞ : Sphere) = if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) :=
  OnePoint.smul_infty_eq_ite g
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution (g : MobiusMatrix) (ha : g 0 0 = 0) (hd : g 1 1 = 0) :
    g 0 1 / g 1 0 ≠ 0 ∧ ∀ p : Sphere, g • p = sphereInversion (g 0 1 / g 1 0) p := by
  have hn := g.det_ne_zero
  simp only [Matrix.det_fin_two, ha, hd, zero_mul, zero_sub, neg_ne_zero, ne_eq,
    mul_eq_zero, not_or] at hn
  refine ⟨div_ne_zero hn.1 hn.2, ?_⟩
  intro p
  cases p using OnePoint.rec with
  | infty => simp [mobius_infinity_formula, ha, hn.2, sphereInversion]
  | coe z =>
    by_cases hz : z = 0
    · simp [mobius_finite_formula, hd, hz, sphereInversion]
    · have he : g 0 1 / (g 1 0 * z) = g 0 1 / g 1 0 / z := by
        field_simp
      simp [mobius_finite_formula, ha, hd, hn.2, hz, sphereInversion, he]
end

#print axioms solution
