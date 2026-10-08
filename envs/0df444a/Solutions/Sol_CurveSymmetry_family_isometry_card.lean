-- Prove2me | solution 1 for CurveSymmetry.family_isometry_card
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:07:10.346866+00:00
-- url     : https://prove2.me/submissions/d35b76c0-fd29-4ebf-a742-989a107fbeca

-- Solution generated from lean/FamilyEuclidean.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_direct_card
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_no_conjugate_affine
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
lemma direct_coeff_ne_zero {S : Set ℂ} {a b : ℂ} (h : DirectSymmetry S a b) : a ≠ 0 := by
  intro hz
  have hnorm := h.1
  simp [hz] at hnorm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma direct_parameters_unique {a b c d : ℂ}
    (h : ∀ z : ℂ, a * z + b = c * z + d) : (a, b) = (c, d) := by
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, zero_add] at h0
  simp only [mul_one] at h1
  apply Prod.ext
  · linear_combination h1 - h0
  · exact h0
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma opposite_parameters_unique {a b c d : ℂ}
    (h : ∀ z : ℂ, a * star z + b = c * star z + d) : (a, b) = (c, d) := by
  apply direct_parameters_unique
  intro z
  simpa using h (star z)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma direct_ne_opposite {a b c d : ℂ} (ha : a ≠ 0)
    (h : ∀ z : ℂ, a * z + b = c * star z + d) : False := by
  have h0 := h 0
  have h1 := h 1
  have hI := h Complex.I
  simp only [star_zero, mul_zero, zero_add] at h0
  simp only [star_one, mul_one] at h1
  have hac : a = c := by linear_combination h1 - h0
  have he : a * Complex.I = a * (-Complex.I) := by
    simpa [← hac, h0] using hI
  have hi := congrArg Complex.im (mul_left_cancel₀ ha he)
  norm_num at hi
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma parametersToIsometry_injective (P : BPoly) : Function.Injective (parametersToIsometry P) := by
  intro u v h
  have he : ∀ z : ℂ, (parametersToIsometry P u).val z = (parametersToIsometry P v).val z :=
    fun z => congrArg (fun f : isometrySymmetryGroup P => f.val z) h
  cases u with
  | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Subtype.ext (direct_parameters_unique he))
      | inr v => exact (direct_ne_opposite (direct_coeff_ne_zero u.prop) he).elim
  | inr u =>
      cases v with
      | inl v => exact (direct_ne_opposite (direct_coeff_ne_zero v.prop) (fun z => (he z).symm)).elim
      | inr v => exact congrArg Sum.inr (Subtype.ext (opposite_parameters_unique he))
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma parametersToIsometry_surjective (P : BPoly) : Function.Surjective (parametersToIsometry P) := by
  intro f
  rcases isometry_affine_forms f.val with ⟨a, b, ha, he⟩ | ⟨a, b, ha, he⟩
  · have hs : DirectSymmetry (realLocus P) a b := ⟨ha, by intro z; rw [← he]; exact f.prop z⟩
    refine ⟨Sum.inl ⟨(a, b), hs⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    exact (he z).symm
  · have hs : OppositeSymmetry (realLocus P) a b := ⟨ha, by intro z; rw [← he]; exact f.prop z⟩
    refine ⟨Sum.inr ⟨(a, b), hs⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    exact (he z).symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable def euclideanIsometryEquiv (P : BPoly) : EuclideanSymmetries P ≃ isometrySymmetryGroup P :=
  Equiv.ofBijective (parametersToIsometry P)
    ⟨parametersToIsometry_injective P, parametersToIsometry_surjective P⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
/-- Normalized family members have no opposite Euclidean symmetry for all
m>=2. The older unnormalized result for m>=3 remains available. -/
theorem family_no_opposite_normalized {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    IsEmpty (OppositeSymmetries (familyPolynomial m α)) := by
  refine ⟨fun g => ?_⟩
  have hga : g.val.1 ≠ 0 := by
    intro hz
    have hn := g.property.1
    simp [hz] at hn
  apply family_no_conjugate_affine hm ha hα hga
  intro z hz
  rw [← family_locus_eq] at hz ⊢
  exact (g.property.2 z).mpr hz
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nat.card (isometrySetGroup (extremalCurve m α)) = 2 * m := by
  let := family_no_opposite_normalized hm ha hα
  rw [← family_locus_eq, ← Nat.card_congr (euclideanIsometryEquiv (familyPolynomial m α))]
  change Nat.card (DirectSymmetries (familyPolynomial m α) ⊕
    OppositeSymmetries (familyPolynomial m α)) = _
  rw [Nat.card_congr (Equiv.sumEmpty _ _)]
  exact family_direct_card hm ha
end

#print axioms solution
