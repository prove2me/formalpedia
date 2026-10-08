-- Prove2me | solution 1 for CurveSymmetry.family_sphere_inversion_filter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:49.216485+00:00
-- url     : https://prove2.me/submissions/a6b1b725-7cfc-481b-b87d-2dfb1dd64d14

-- Solution generated from lean/FamilySphereInversion.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_inversion_parameter
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_sphere_inversion_proportional
import Theorems.Thm_CurveSymmetry_fourTermForm_proportional_iff
import Theorems.Thm_CurveSymmetry_sphericalFamily_eq
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
set_option autoImplicit false
open MvPolynomial
lemma mul_star_eq_one_of_norm {a : ℂ} (ha : ‖a‖ = 1) : a * star a = 1 := by
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  change a * (starRingEnd ℂ) a = 1
  rw [← Complex.inv_eq_conj ha, mul_inv_cancel₀ hn]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_C (x y c : ℂ) : planeEval x y (C c) = c := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_zero (x y : ℂ) : planeEval x y (X 0) = x := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_one (x y : ℂ) : planeEval x y (X 1) = y := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_eval (m : ℕ) (a b c d x y : ℂ) :
    planeEval x y (fourTermForm m a b c d) =
      a * x ^ m + b * y ^ m + x * y * (c * x ^ m + d * y ^ m) := by
  simp [fourTermForm, binaryForm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma family_fourTerm (m : ℕ) (α : ℂ) :
    familyPolynomial m α = fourTermForm m α (star α) 1 1 := by
  simp only [familyPolynomial, fourTermForm, binaryForm, map_one, one_mul]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- This is the actual denominator-cleared pullback by `(X,Y) ↦ (c/X,conj(c)/Y)`. -/
lemma inversionFamily_eval (m : ℕ) (β c : ℂ) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    planeEval x y (inversionFamily m β c) =
      (x * y) ^ (m + 1) * planeEval (c / x) (star c / y) (familyPolynomial m β) := by
  rw [inversionFamily, family_fourTerm, fourTermForm_eval, fourTermForm_eval]
  simp only [mul_pow, pow_succ, div_pow, one_mul]
  field_simp
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma unit_power_product (m : ℕ) {c : ℂ} (hc : ‖c‖ = 1) : c ^ m * star c ^ m = 1 := by
  rw [← mul_pow, mul_star_eq_one_of_norm hc, one_pow]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem family_inversion_filter {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (hc : c ≠ 0) :
    (∃ k : ℂ, inversionFamily m α c = C k * familyPolynomial m α) ↔
      c ^ (2 * m) = star α ^ 2 := by
  constructor
  · rintro ⟨k, he⟩
    have hn := (family_inversion_parameter hm hα hα hc he).1
    rw [inversionFamily, family_fourTerm] at he
    obtain ⟨_, hlow, hhigh, _⟩ := (fourTermForm_proportional_iff hm _ _ _ _ _ _ _ _ _).mp he
    rw [mul_star_eq_one_of_norm hn, mul_one] at hlow
    rw [mul_one] at hhigh
    have hp : c ^ m = star c ^ m * star α ^ 2 := by
      rw [hlow, ← hhigh]
      ring
    calc
      c ^ (2 * m) = c ^ m * c ^ m := by rw [two_mul, pow_add]
      _ = c ^ m * (star c ^ m * star α ^ 2) := congrArg (fun w => c ^ m * w) hp
      _ = star α ^ 2 := by rw [← mul_assoc, unit_power_product m hn, one_mul]
  · intro hroot
    have hn : ‖c‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega : 2 * m ≠ 0)).mp
      simpa [norm_pow, norm_star, hα] using congrArg norm hroot
    have hp : c ^ m = star c ^ m * star α ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero m hc)
      rw [← mul_assoc, unit_power_product m hn, one_mul, ← pow_add, ← two_mul, hroot]
    have ha := mul_star_eq_one_of_norm hα
    refine ⟨star c ^ m * star α, ?_⟩
    rw [inversionFamily, family_fourTerm, fourTermForm_proportional_iff hm,
      mul_star_eq_one_of_norm hn]
    refine ⟨?_, ?_, by ring, ?_⟩
    · linear_combination -(star c ^ m) * ha
    · simpa only [mul_one, mul_assoc, pow_two] using hp
    · rw [hp]
      linear_combination star c ^ m * star α * ha
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
theorem finite_mem_sphericalFamily_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (z : ℂ) :
    (z : Sphere) ∈ sphericalFamily m α ↔ z ∈ extremalCurve m α := by
  rw [sphericalFamily_eq hm ha]
  simp only [Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
    Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
theorem infinity_mem_sphericalFamily {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) : (∞ : Sphere) ∈ sphericalFamily m α := by
  rw [sphericalFamily_eq hm ha]
  exact Set.mem_insert _ _
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
theorem solution {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0) :
    (∀ p ∈ sphericalFamily m α, sphereInversion c p ∈ sphericalFamily m α) ↔
      c ^ (2 * m) = star α ^ 2 := by
  constructor
  · intro hmap
    obtain ⟨k, _, he⟩ := family_sphere_inversion_proportional hm ha ha hc hmap
    exact (family_inversion_filter hm hα hc).mp ⟨k, he⟩
  · intro hroot p hp
    obtain ⟨k, he⟩ := (family_inversion_filter hm hα hc).mpr hroot
    cases p using OnePoint.rec with
    | infty =>
      simp only [sphereInversion, OnePoint.elim_infty]
      rw [finite_mem_sphericalFamily_iff hm ha]
      simp [extremalCurve, hm.ne']
    | coe z =>
      by_cases hz : z = 0
      · simp only [sphereInversion, hz, OnePoint.elim_some]
        exact infinity_mem_sphericalFamily hm ha
      · change (if z = 0 then ∞ else ((c / z : ℂ) : Sphere)) ∈ sphericalFamily m α
        rw [if_neg hz]
        rw [finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq] at hp ⊢
        change planeEval z (star z) (familyPolynomial m α) = 0 at hp
        change planeEval (c / z) (star (c / z)) (familyPolynomial m α) = 0
        have hev := congrArg (planeEval z (star z)) he
        rw [inversionFamily_eval m α c hz (star_ne_zero.mpr hz), map_mul,
          planeEval_C, hp, mul_zero] at hev
        have hs : star (c / z) = star c / star z := map_div₀ (starRingEnd ℂ) c z
        rw [hs]
        exact (mul_eq_zero.mp hev).resolve_left
          (pow_ne_zero _ (mul_ne_zero hz (star_ne_zero.mpr hz)))
end

#print axioms solution
