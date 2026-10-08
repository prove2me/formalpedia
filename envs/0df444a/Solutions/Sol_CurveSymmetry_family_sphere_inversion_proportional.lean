-- Prove2me | solution 1 for CurveSymmetry.family_sphere_inversion_proportional
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:19.902149+00:00
-- url     : https://prove2.me/submissions/2b12c5d7-0ca7-4c0e-aa5e-b29e5e44eadf

-- Solution generated from lean/FamilySphereInversion.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_point_of_norm
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
/-- A same-degree equation vanishing on the real curve differs by a nonzero scalar. -/
theorem proportional_of_realLocus_subset {P Q : BPoly} (hP : Irreducible P)
    (hQ : Q ≠ 0) (hinf : (realLocus P).Infinite)
    (hsub : realLocus P ⊆ realLocus Q) (hdeg : Q.totalDegree ≤ P.totalDegree) :
    ∃ c : ℂ, c ≠ 0 ∧ Q = C c * P := by
  obtain ⟨S, hS⟩ := dvd_of_realLocus_subset hP hinf hsub
  have hs0 : S ≠ 0 := by intro hs; apply hQ; simp [hS, hs]
  have hdegree := totalDegree_mul_of_isDomain hP.ne_zero hs0
  have hdS : S.totalDegree = 0 := by rw [← hS] at hdegree; omega
  have hcS : S = C (S.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hdS
  refine ⟨S.coeff 0, ?_, ?_⟩
  · intro hc
    exact hs0 (by simpa [hc] using hcS)
  · rw [hS, hcS, mul_comm]
    simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem family_realLocus_infinite {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (realLocus (familyPolynomial m α)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = (n : ℝ) + 1 := by
    intro n
    exact family_point_of_norm hm ha (by positivity)
  choose f hf hnorm using hex
  have hinj : Function.Injective f := by
    intro n k h
    have he := congrArg norm h
    rw [hnorm, hnorm] at he
    exact_mod_cast (add_right_cancel he)
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨n, rfl⟩; exact hf n)
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
lemma fourTermForm_monomial (m : ℕ) (a b c d : ℂ) :
    fourTermForm m a b c d = monomial (exponent m 0) a + monomial (exponent 0 m) b +
      monomial (exponent (m + 1) 1) c + monomial (exponent 1 (m + 1)) d := by
  simp only [fourTermForm, binaryForm, monomial_exponent, pow_zero, pow_succ, mul_one]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_coefficients {m : ℕ} (hm : 0 < m) (a b c d : ℂ) :
    (fourTermForm m a b c d).coeff (exponent m 0) = a ∧
      (fourTermForm m a b c d).coeff (exponent 0 m) = b ∧
      (fourTermForm m a b c d).coeff (exponent (m + 1) 1) = c ∧
      (fourTermForm m a b c d).coeff (exponent 1 (m + 1)) = d := by
  rw [fourTermForm_monomial]
  simp [coeff_monomial, exponent_eq_iff, hm.ne']
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
open MvPolynomial OnePoint
private lemma inversion_degree_le (m : ℕ) (β c : ℂ) :
    (inversionFamily m β c).totalDegree ≤ m + 2 := by
  have hb (a b : ℕ) (k : ℂ) :
      (monomial (exponent a b) k : BPoly).totalDegree ≤ a + b := by
    simpa [Function.id_def, exponent_degree] using totalDegree_monomial_le (exponent a b) k
  rw [inversionFamily, fourTermForm_monomial]
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le ((hb _ _ _).trans (by omega)) ((hb _ _ _).trans (by omega))
    · exact (hb _ _ _).trans (by omega)
  · exact (hb _ _ _).trans (by omega)
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
theorem solution {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereInversion c p ∈ sphericalFamily m β) :
    ∃ k : ℂ, k ≠ 0 ∧ inversionFamily m β c = C k * familyPolynomial m α := by
  apply proportional_of_realLocus_subset (familyPolynomial_irreducible hm ha)
    (hinf := family_realLocus_infinite hm ha)
  · intro he
    have hcoef := (fourTermForm_coefficients hm
      (star c ^ m * (c * star c)) (c ^ m * (c * star c))
      (star c ^ m * star β) (c ^ m * β)).1
    change (inversionFamily m β c).coeff (exponent m 0) = _ at hcoef
    rw [he, MvPolynomial.coeff_zero] at hcoef
    exact (mul_ne_zero (pow_ne_zero m (star_ne_zero.mpr hc))
      (mul_ne_zero hc (star_ne_zero.mpr hc))) hcoef.symm
  · intro z hz
    change planeEval z (star z) (inversionFamily m β c) = 0
    by_cases hz0 : z = 0
    · simp [hz0, inversionFamily, fourTermForm_eval, hm.ne']
    · have hzs : (z : Sphere) ∈ sphericalFamily m α := by
        rw [finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq]
        exact hz
      have ht := hmap (z : Sphere) hzs
      change (if z = 0 then ∞ else ((c / z : ℂ) : Sphere)) ∈ sphericalFamily m β at ht
      rw [if_neg hz0] at ht
      rw [finite_mem_sphericalFamily_iff hm hb, ← family_locus_eq] at ht
      change planeEval (c / z) (star (c / z)) (familyPolynomial m β) = 0 at ht
      rw [inversionFamily_eval m β c hz0 (star_ne_zero.mpr hz0)]
      have hs : star (c / z) = star c / star z := map_div₀ (starRingEnd ℂ) c z
      rw [← hs, ht, mul_zero]
  · rw [family_degree hm]
    exact inversion_degree_le m β c
end

#print axioms solution
