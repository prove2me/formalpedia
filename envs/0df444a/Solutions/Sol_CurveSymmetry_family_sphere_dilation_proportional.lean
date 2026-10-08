-- Prove2me | solution 1 for CurveSymmetry.family_sphere_dilation_proportional
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:18.955493+00:00
-- url     : https://prove2.me/submissions/dbc898ad-e495-4e06-963b-359008add94d

-- Solution generated from lean/FamilySphereDilation.lean (curve-symmetry-lean): inlined helpers in
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
lemma fourTermForm_totalDegree_le (m : ℕ) (a b c d : ℂ) :
    (fourTermForm m a b c d).totalDegree ≤ m + 2 := by
  rw [fourTermForm_monomial]
  have h (i j : ℕ) (k : ℂ) :
      (monomial (exponent i j) k : BPoly).totalDegree ≤ i + j := by
    simpa [Function.id_def, exponent_degree] using totalDegree_monomial_le (exponent i j) k
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le ((h m 0 a).trans (by omega)) ((h 0 m b).trans (by omega))
    · exact (h (m + 1) 1 c).trans (by omega)
  · exact (h 1 (m + 1) d).trans (by omega)
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
theorem solution {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m β) :
    ∃ k : ℂ, k ≠ 0 ∧ dilate c (familyPolynomial m β) = C k * familyPolynomial m α := by
  apply proportional_of_realLocus_subset (familyPolynomial_irreducible hm ha)
  · intro he
    have ht := (fourTermForm_coefficients hm (c ^ m * β)
      (star c ^ m * star β) (c ^ m * (c * star c)) (star c ^ m * (c * star c))).2.2.1
    rw [← dilate_family_fourTerm, he, MvPolynomial.coeff_zero] at ht
    exact (mul_ne_zero (pow_ne_zero m hc) (mul_ne_zero hc (star_ne_zero.mpr hc))) ht.symm
  · exact family_realLocus_infinite hm ha
  · intro z hz
    have hp : (z : Sphere) ∈ sphericalFamily m α :=
      (finite_mem_sphericalFamily_iff hm ha z).mpr ((family_locus_eq m α) ▸ hz)
    have hq := hmap (z : Sphere) hp
    change eval _ (dilate c (familyPolynomial m β)) = 0
    rw [eval_dilate]
    change c * z ∈ realLocus (familyPolynomial m β)
    exact (family_locus_eq m β).symm ▸
      ((finite_mem_sphericalFamily_iff hm hb (c * z)).mp hq)
  · rw [dilate_family_fourTerm, family_degree hm]
    exact fourTermForm_totalDegree_le _ _ _ _ _
end

#print axioms solution
