-- Prove2me | solution 1 for CurveSymmetry.reflection_fixes_equation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:53.236815+00:00
-- url     : https://prove2.me/submissions/fe4a733c-37b5-4a32-938e-67c6d1fbfa67

-- Solution generated from lean/Reflection.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
import Theorems.Thm_CurveSymmetry_lineEquation_degree
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
/-- A nonunit divisor of an irreducible polynomial has the same degree. -/
lemma degree_le_of_nonunit_dvd {P L : BPoly} (hP : Irreducible P)
    (hL : ¬ IsUnit L) (hdiv : L ∣ P) : P.totalDegree ≤ L.totalDegree := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hunit : IsUnit Q := (hP.isUnit_or_isUnit hQ).resolve_left hL
  have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  rw [hQ]
  simpa [hzero] using totalDegree_mul L Q
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
lemma rotate_degree_le (ζ : ℂ) (P : BPoly) : (rotate ζ P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_le_of_support_subset
  intro s hs
  rw [mem_support_iff, coeff_rotate] at hs
  exact mem_support_iff.mpr (mul_ne_zero_iff.mp hs).1
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_lineEquation (z v w : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then w else star w) (lineEquation z v) =
      star v * w - v * star w - (star v * z - v * star z) := by
  simp [lineEquation]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma lineEquation_irreducible (z v : ℂ) (hv : v ≠ 0) : Irreducible (lineEquation z v) := by
  have hd := lineEquation_degree z v hv
  apply irreducible_of_totalDegree_eq_one hd
  intro a ha
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hzero : lineEquation z v = 0 := by
    ext s
    have h := ha s
    simpa [hz] using h
  simp [hzero] at hd
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma lineEquation_realLocus_infinite (z v : ℂ) (hv : v ≠ 0) :
    (realLocus (lineEquation z v)).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => z + v * (n : ℂ)) := by
    intro n m h
    have hnm : (n : ℂ) = m := mul_left_cancel₀ hv (add_left_cancel h)
    exact_mod_cast hnm
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  change eval _ (lineEquation z v) = 0
  rw [eval_lineEquation]
  simp only [star_add, star_mul, star_natCast]
  ring
end CurveSymmetry

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
lemma reflect_involutive {a : ℂ} (ha : ‖a‖ = 1) (P : BPoly) :
    reflect a (reflect a P) = P := by
  have hc := mul_star_eq_one_of_norm ha
  have h0 : reflect a (X 0) = C a * X 1 := by simp [reflect]
  have h1 : reflect a (X 1) = C (star a) * X 0 := by simp [reflect]
  have hC : ∀ c : ℂ, reflect a (C c) = C c := by intro c; simp [reflect]
  induction P using MvPolynomial.induction_on with
  | C c => simp [reflect]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i
      · change P * reflect a (reflect a (X 0)) = P * X 0
        rw [h0, map_mul, hC, h1, ← mul_assoc (C a), ← C_mul, hc, C_1, one_mul]
      · change P * reflect a (reflect a (X 1)) = P * X 1
        rw [h1, map_mul, hC, h0, ← mul_assoc (C (star a)), ← C_mul,
          mul_comm (star a) a, hc, C_1, one_mul]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma reflect_ne_zero {a : ℂ} (ha : ‖a‖ = 1) {P : BPoly} (hP : P ≠ 0) :
    reflect a P ≠ 0 := by
  intro h
  have he := reflect_involutive ha P
  rw [h, map_zero] at he
  exact hP he.symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma reflect_degree_le {a : ℂ} (ha : ‖a‖ = 1) (P : BPoly) :
    (reflect a P).totalDegree ≤ P.totalDegree := by
  have he : reflect a P = rename (Equiv.swap (0 : Fin 2) 1) (rotate a P) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp [reflect, rotate]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P i hP =>
        simp only [map_mul, hP]
        fin_cases i <;> simp [reflect, rotate, Complex.inv_eq_conj ha]
  rw [he]
  exact (totalDegree_rename_le _ _).trans (rotate_degree_le a P)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_reflect (a : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (reflect a P) =
      eval (fun i : Fin 2 => if i = 0 then a * star z else star (a * star z)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [reflect]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [reflect, star_mul, mul_comm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma reflection_fixed_direction {a : ℂ} (ha : ‖a‖ = 1) :
    ∃ v : ℂ, v ≠ 0 ∧ a * star v = v := by
  have hc := mul_star_eq_one_of_norm ha
  by_cases h : a = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    simp [h]
  · refine ⟨1 + a, by intro hz; apply h; linear_combination hz, ?_⟩
    simp only [star_add, star_one, mul_add, mul_one, hc]
    ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) {a : ℂ}
    (ha : ‖a‖ = 1) (hsym : ∀ z ∈ realLocus P, a * star z ∈ realLocus P) :
    reflect a P = P := by
  have hsub : realLocus P ⊆ realLocus (reflect a P) := by
    intro z hz
    change eval _ (reflect a P) = 0
    rw [eval_reflect]
    exact hsym z hz
  obtain ⟨c, _, hp⟩ := proportional_of_realLocus_subset hP
    (reflect_ne_zero ha hP.ne_zero) hinf hsub (reflect_degree_le ha P)
  by_cases hc : c = 1
  · simpa [hc] using hp
  obtain ⟨v, hv, hfix⟩ := reflection_fixed_direction ha
  have hline : realLocus (lineEquation 0 v) ⊆ realLocus P := by
    intro z hz
    change eval _ (lineEquation 0 v) = 0 at hz
    rw [eval_lineEquation] at hz
    simp only [mul_zero, star_zero, sub_zero] at hz
    have hf : a * star z = z := by
      apply mul_left_cancel₀ (star_ne_zero.mpr hv)
      linear_combination -hz + star z * hfix
    have he := congrArg (eval (fun i : Fin 2 => if i = 0 then z else star z)) hp
    rw [eval_reflect, hf, map_mul, eval_C] at he
    have hh : (1 - c) * eval (fun i : Fin 2 => if i = 0 then z else star z) P = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  have hL := lineEquation_irreducible 0 v hv
  have hdiv := dvd_of_realLocus_subset hL (lineEquation_realLocus_infinite 0 v hv) hline
  have hb := degree_le_of_nonunit_dvd hP hL.not_isUnit hdiv
  rw [lineEquation_degree 0 v hv] at hb
  omega
end

#print axioms solution
