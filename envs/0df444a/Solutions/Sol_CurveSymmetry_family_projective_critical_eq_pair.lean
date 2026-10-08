-- Prove2me | solution 1 for CurveSymmetry.family_projective_critical_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:47.564626+00:00
-- url     : https://prove2.me/submissions/59c5abc2-0473-4779-a8b2-0f321064478e

-- Solution generated from lean/FamilyGlobalSingularities.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_projective_critical_pair
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

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) :
    familyProjectiveCritical m α =
      {(sphereProjectiveEquiv ((0 : ℂ) : Sphere), sphereProjectiveEquiv ((0 : ℂ) : Sphere)),
        (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere))} := by
  ext ⟨p, q⟩
  obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
  obtain ⟨v, rfl⟩ := sphereProjectiveEquiv.surjective q
  rw [family_projective_critical_pair hm ha]
  simp
end

#print axioms solution
