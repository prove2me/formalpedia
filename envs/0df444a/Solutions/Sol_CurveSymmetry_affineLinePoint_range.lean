-- Prove2me | solution 1 for CurveSymmetry.affineLinePoint_range
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:24.297068+00:00
-- url     : https://prove2.me/submissions/0fc3f41c-058a-438e-8831-e56a9510dec6

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

section
open CurveSymmetry
open OnePoint
set_option autoImplicit false
theorem solution (p : ProjectiveLine) :
    p ∈ Set.range affineLinePoint ↔ p ≠ sphereProjectiveEquiv (∞ : Sphere) := by
  obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
  cases u using OnePoint.rec with
  | infty =>
      constructor
      · rintro ⟨z, hz⟩
        change sphereProjectiveEquiv (z : Sphere) = sphereProjectiveEquiv ∞ at hz
        exact (OnePoint.coe_ne_infty z (sphereProjectiveEquiv.injective hz)).elim
      · intro h; exact (h rfl).elim
  | coe z =>
      constructor
      · intro _ h
        exact OnePoint.coe_ne_infty z (sphereProjectiveEquiv.injective h)
      · intro _; exact ⟨z, rfl⟩
end

#print axioms solution
