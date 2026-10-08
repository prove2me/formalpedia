-- Prove2me | solution 1 for CurveSymmetry.reciprocalLinePoint_range
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:33.794683+00:00
-- url     : https://prove2.me/submissions/5941d69f-b831-4a44-9add-69d418bd6dfe

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
theorem reciprocalLinePoint_overlap {z : ℂ} (hz : z ≠ 0) :
    reciprocalLinePoint z = affineLinePoint z⁻¹ := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z, ?_⟩
  ext i
  fin_cases i <;> simp [hz]
end
end CurveSymmetry

section
open CurveSymmetry
open OnePoint
set_option autoImplicit false
theorem solution (p : ProjectiveLine) :
    p ∈ Set.range reciprocalLinePoint ↔ p ≠ affineLinePoint 0 := by
  constructor
  · rintro ⟨z, rfl⟩ h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    have h0 := congrFun ha 0
    simp at h0
  · intro hp
    obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
    cases u using OnePoint.rec with
    | infty => exact ⟨0, rfl⟩
    | coe z =>
        have hz : z ≠ 0 := by intro h; subst z; exact hp rfl
        refine ⟨z⁻¹, ?_⟩
        rw [reciprocalLinePoint_overlap (inv_ne_zero hz), inv_inv]
        rfl
end

#print axioms solution
