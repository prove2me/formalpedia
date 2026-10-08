-- Prove2me | solution 1 for CurveSymmetry.isometry_affine_forms
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:08.461803+00:00
-- url     : https://prove2.me/submissions/e99f613c-fc87-46ae-a78c-3767da1797ec

-- Solution generated from lean/IsometryInterface.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
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

section
open CurveSymmetry
set_option autoImplicit false
theorem solution (f : ℂ ≃ᵢ ℂ) :
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * z + b) ∨
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * star z + b) := by
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex f.toRealLinearIsometryEquiv
  · left
    refine ⟨a, f 0, Circle.norm_coe a, ?_⟩
    intro z
    have he := congrArg (fun L : ℂ ≃ₗᵢ[ℝ] ℂ => L z) ha
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply, rotation_apply] at he
    exact eq_add_of_sub_eq he
  · right
    refine ⟨a, f 0, Circle.norm_coe a, ?_⟩
    intro z
    have he := congrArg (fun L : ℂ ≃ₗᵢ[ℝ] ℂ => L z) ha
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply] at he
    exact eq_add_of_sub_eq he
end

#print axioms solution
