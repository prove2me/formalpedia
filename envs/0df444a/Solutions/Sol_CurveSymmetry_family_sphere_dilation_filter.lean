-- Prove2me | solution 1 for CurveSymmetry.family_sphere_dilation_filter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:48.415987+00:00
-- url     : https://prove2.me/submissions/1af240da-f18d-43f8-9415-159bdb5ca318

-- Solution generated from lean/FamilySphereDilation.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_dilation_parameter
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_sphere_dilation_proportional
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
lemma eval_dilate (c : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (dilate c P) =
      eval (fun i : Fin 2 => if i = 0 then c * z else star (c * z)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [dilate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [dilate, star_mul, mul_comm]
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
lemma dilate_family_fourTerm (m : ℕ) (β c : ℂ) :
    dilate c (familyPolynomial m β) = fourTermForm m (c ^ m * β)
      (star c ^ m * star β) (c ^ m * (c * star c)) (star c ^ m * (c * star c)) := by
  simp only [familyPolynomial, map_add, map_mul, map_pow]
  have h0 : dilate c (X 0) = C c * X 0 := by simp [dilate]
  have h1 : dilate c (X 1) = C (star c) * X 1 := by simp [dilate]
  have hC : ∀ a : ℂ, dilate c (C a) = C a := by intro a; simp [dilate]
  rw [h0, h1, hC, hC]
  simp only [fourTermForm, binaryForm, mul_pow, map_pow, map_mul]
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
theorem family_dilation_filter {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (hc : c ≠ 0) :
    (∃ k : ℂ, dilate c (familyPolynomial m α) = C k * familyPolynomial m α) ↔
      c ^ (2 * m) = 1 := by
  constructor
  · rintro ⟨k, he⟩
    have hn := (family_dilation_parameter hm hα hα hc he).1
    rw [dilate_family_fourTerm, family_fourTerm] at he
    obtain ⟨_, _, h0, h1⟩ := (fourTermForm_proportional_iff hm _ _ _ _ _ _ _ _ _).mp he
    rw [mul_star_eq_one_of_norm hn, mul_one, mul_one] at h0 h1
    have hp : c ^ m = star c ^ m := h0.trans h1.symm
    calc
      c ^ (2 * m) = c ^ m * c ^ m := by rw [two_mul, pow_add]
      _ = c ^ m * star c ^ m := congrArg (fun w => c ^ m * w) hp
      _ = 1 := unit_power_product m hn
  · intro hroot
    have hn : ‖c‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega : 2 * m ≠ 0)).mp
      simpa using congrArg norm hroot
    have hp : c ^ m = star c ^ m := by
      apply mul_left_cancel₀ (pow_ne_zero m hc)
      rw [unit_power_product m hn, ← pow_add, ← two_mul, hroot]
    refine ⟨c ^ m, ?_⟩
    rw [dilate_family_fourTerm, family_fourTerm, fourTermForm_proportional_iff hm,
      mul_star_eq_one_of_norm hn]
    simp [hp]
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
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0) :
    (∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m α) ↔
      c ^ (2 * m) = 1 := by
  constructor
  · intro hmap
    obtain ⟨k, _, hk⟩ := family_sphere_dilation_proportional hm ha ha hc hmap
    exact (family_dilation_filter hm hα hc).mp ⟨k, hk⟩
  · intro hroot p hp
    obtain ⟨k, hk⟩ := (family_dilation_filter hm hα hc).mpr hroot
    cases p using OnePoint.rec with
    | infty => simpa [sphereDilation] using infinity_mem_sphericalFamily hm ha
    | coe z =>
      have hz : z ∈ realLocus (familyPolynomial m α) :=
        (family_locus_eq m α).symm ▸ ((finite_mem_sphericalFamily_iff hm ha z).mp hp)
      apply (finite_mem_sphericalFamily_iff hm ha (c * z)).mpr
      rw [← family_locus_eq]
      change eval _ (familyPolynomial m α) = 0
      rw [← eval_dilate, hk, map_mul, hz, mul_zero]
end

#print axioms solution
