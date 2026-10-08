-- Prove2me | solution 1 for CurveSymmetry.rotation_sign_of_realLocus
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:54.016467+00:00
-- url     : https://prove2.me/submissions/4374fed3-24aa-4cf6-b41d-a711cf449c2f

-- Solution generated from lean/GeometricRotation.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma rotate_monomial (ζ : ℂ) (s : Exponent) (c : ℂ) :
    rotate ζ (monomial s c) = monomial s (c * (ζ ^ s 0 * (ζ⁻¹) ^ s 1)) := by
  simp only [rotate, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, mul_pow,
    ← map_pow C, X_pow_eq_monomial]
  rw [show s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) from exponent_decompose s]
  simp only [C_mul_monomial, monomial_mul, mul_one]
  simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma coeff_rotate (ζ : ℂ) (P : BPoly) (s : Exponent) :
    (rotate ζ P).coeff s = P.coeff s * (ζ ^ s 0 * (ζ⁻¹) ^ s 1) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial t c =>
      rw [rotate_monomial]
      by_cases h : t = s
      · subst t; simp
      · simp [coeff_monomial, h]
  | add P Q hP hQ => simp [map_add, hP, hQ, add_mul]
end CurveSymmetry

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
lemma coeff_conjugateSwap (P : BPoly) (a b : ℕ) :
    (conjugateSwap P).coeff (exponent b a) = star (P.coeff (exponent a b)) := by
  have he : (exponent a b).mapDomain (Equiv.swap (0 : Fin 2) 1) = exponent b a := by
    simp [exponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, add_comm]
  simp only [conjugateSwap, RingHom.comp_apply, coeff_map]
  change star ((rename (Equiv.swap (0 : Fin 2) 1) P).coeff (exponent b a)) = _
  rw [← he, coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 2) 1).injective]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma conjugateSwap_ne_zero {P : BPoly} (hP : P ≠ 0) : conjugateSwap P ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  intro hzero
  have h := coeff_conjugateSwap P (s 0) (s 1)
  rw [hzero, MvPolynomial.coeff_zero] at h
  apply hs
  rw [he]
  exact star_eq_zero.mp h.symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma conjugateSwap_degree_le (P : BPoly) : (conjugateSwap P).totalDegree ≤ P.totalDegree := by
  exact (totalDegree_le_of_support_subset (support_map_subset _ _)).trans
    (totalDegree_rename_le _ _)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_conjugateSwap (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (conjugateSwap P) =
      star (eval (fun i : Fin 2 => if i = 0 then z else star z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [conjugateSwap]
  | add P Q hP hQ => simp only [map_add, hP, hQ, star_add]
  | mul_X P i hP =>
      simp only [map_mul, hP, star_mul]
      fin_cases i <;> simp [conjugateSwap, mul_comm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Infinite real locus forces symmetric monomial support, without a reality assumption. -/
lemma realLocus_support_symmetric {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) {a b : ℕ}
    (hc : P.coeff (exponent a b) ≠ 0) : P.coeff (exponent b a) ≠ 0 := by
  have hsub : realLocus P ⊆ realLocus (conjugateSwap P) := by
    intro z hz
    change eval _ (conjugateSwap P) = 0
    rw [eval_conjugateSwap, hz, star_zero]
  obtain ⟨c, _, hprop⟩ := proportional_of_realLocus_subset hP
    (conjugateSwap_ne_zero hP.ne_zero) hinf hsub (conjugateSwap_degree_le P)
  have he := congrArg (fun Q : BPoly => Q.coeff (exponent b a)) hprop
  rw [coeff_conjugateSwap, coeff_C_mul] at he
  intro hzero
  rw [hzero, mul_zero] at he
  exact hc (star_eq_zero.mp he)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma rotate_degree_le (ζ : ℂ) (P : BPoly) : (rotate ζ P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_le_of_support_subset
  intro s hs
  rw [mem_support_iff, coeff_rotate] at hs
  exact mem_support_iff.mpr (mul_ne_zero_iff.mp hs).1
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma rotate_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) {P : BPoly} (hP : P ≠ 0) : rotate ζ P ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
  intro hzero
  have he := coeff_rotate ζ P s
  rw [hzero, MvPolynomial.coeff_zero] at he
  exact (mul_ne_zero hs (mul_ne_zero (pow_ne_zero _ hζ)
    (pow_ne_zero _ (inv_ne_zero hζ)))) he.symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_rotate (ζ : ℂ) (hnorm : ‖ζ‖ = 1) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (rotate ζ P) =
      eval (fun i : Fin 2 => if i = 0 then ζ * z else star (ζ * z)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rotate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [rotate, Complex.inv_eq_conj hnorm, star_mul, mul_comm]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) {ζ : ℂ} (hnorm : ‖ζ‖ = 1)
    (hsym : ∀ z ∈ realLocus P, ζ * z ∈ realLocus P) :
    rotate ζ P = P ∨ rotate ζ P = -P := by
  have hz : ζ ≠ 0 := by intro h; simp [h] at hnorm
  have hsub : realLocus P ⊆ realLocus (rotate ζ P) := by
    intro z hz
    change eval _ (rotate ζ P) = 0
    rw [eval_rotate ζ hnorm]
    exact hsym z hz
  obtain ⟨c, _, hprop⟩ := proportional_of_realLocus_subset hP
    (rotate_ne_zero hz hP.ne_zero) hinf hsub (rotate_degree_le ζ P)
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP.ne_zero
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  have hs' : P.coeff (exponent (s 0) (s 1)) ≠ 0 := by simpa [← he] using hs
  have ht := realLocus_support_symmetric hP hinf hs'
  have hchar : ∀ a b, P.coeff (exponent a b) ≠ 0 → ζ ^ a * (ζ⁻¹) ^ b = c := by
    intro a b hc
    have h := congrArg (fun Q : BPoly => Q.coeff (exponent a b)) hprop
    rw [coeff_rotate, coeff_C_mul] at h
    simp only [exponent_zero, exponent_one] at h
    apply mul_left_cancel₀ hc
    simpa [mul_comm] using h
  have h1 := hchar (s 0) (s 1) hs'
  have h2 := hchar (s 1) (s 0) ht
  have hc : c ^ 2 = 1 := by
    calc
      c ^ 2 = (ζ ^ s 0 * (ζ⁻¹) ^ s 1) * (ζ ^ s 1 * (ζ⁻¹) ^ s 0) := by rw [h1, h2]; ring
      _ = 1 := by rw [inv_pow, inv_pow]; field_simp
  rcases sq_eq_one_iff.mp hc with hc | hc
  · left; simpa [hc] using hprop
  · right; simpa [hc] using hprop
end

#print axioms solution
