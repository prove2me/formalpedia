-- Prove2me | solution 1 for CurveSymmetry.family_isometry_iff_rotation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:07:11.354573+00:00
-- url     : https://prove2.me/submissions/fe61d7f4-f6b6-44dd-bc0d-688f8d5cb367

-- Solution generated from lean/FamilyEuclidean.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_affine_self_filter
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_no_conjugate_affine
import Theorems.Thm_CurveSymmetry_family_root_symmetry
import Theorems.Thm_CurveSymmetry_isometry_affine_forms
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
open OnePoint
noncomputable section
/-- Every actual Euclidean self-isometry is direct, including m=2.
The translation coefficient is not yet eliminated by this endpoint. -/
theorem family_isometry_direct {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (f : ℂ ≃ᵢ ℂ)
    (hf : ∀ z ∈ extremalCurve m α, f z ∈ extremalCurve m α) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z, f z = a * z + b := by
  rcases isometry_affine_forms f with h | ⟨a, b, hn, he⟩
  · exact h
  · have ha0 : a ≠ 0 := by intro hz; simp [hz] at hn
    exact False.elim (family_no_conjugate_affine hm ha hα ha0
      (fun z hz => (he z) ▸ hf z hz))
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (f : ℂ ≃ᵢ ℂ) :
    (∀ z, f z ∈ extremalCurve m α ↔ z ∈ extremalCurve m α) ↔
      ∃ a : ℂ, a ^ (2 * m) = 1 ∧ ∀ z, f z = a * z := by
  constructor
  · intro hf
    obtain ⟨a, b, hn, he⟩ := family_isometry_direct hm ha hα f
      (fun z hz => (hf z).mpr hz)
    have ha0 : a ≠ 0 := by intro hz; simp [hz] at hn
    obtain ⟨hb, hr⟩ := family_affine_self_filter hm ha hα ha0
      (fun z hz => (he z) ▸ (hf z).mpr hz)
    exact ⟨a, hr, fun z => by simpa [hb] using he z⟩
  · rintro ⟨a, hr, he⟩ z
    have hs := family_root_symmetry (by omega : 0 < m) hr α
    rw [he, ← family_locus_eq]
    simpa only [add_zero] using hs.2 z
end

#print axioms solution
