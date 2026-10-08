-- Prove2me | solution 1 for CurveSymmetry.centeredRotationGroup_finite
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:12.695738+00:00
-- url     : https://prove2.me/submissions/0214b470-5310-4e05-b2bf-772128de3e5e

-- Solution generated from lean/RotationGroup.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_irreducible_radial_form
import Theorems.Thm_CurveSymmetry_radial_realLocus_is_circle
import Theorems.Thm_CurveSymmetry_rotation_sign_of_realLocus
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
lemma rotationValue_injective (P : BPoly) : Function.Injective (rotationValue P) := by
  intro u v h
  apply Subtype.ext
  exact Units.ext h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma exists_off_diagonal_coeff {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    ∃ a b : ℕ, a ≠ b ∧ P.coeff (exponent a b) ≠ 0 := by
  by_contra h
  push Not at h
  apply hcircle
  apply radial_realLocus_is_circle hinf
  apply irreducible_radial_form hP
  intro s hs
  by_contra hne
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  exact (mem_support_iff.mp hs) (by rw [he]; exact h (s 0) (s 1) hne)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma rotation_value_root {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) {a b : ℕ}
    (hc : P.coeff (exponent a b) ≠ 0) (u : centeredRotationGroup P) :
    (rotationValue P u) ^ (2 * a) = (rotationValue P u) ^ (2 * b) := by
  have hsign := rotation_sign_of_realLocus hP hinf u.prop.1
    (fun z hz => (u.prop.2 z).mpr hz)
  have hchar : (rotationValue P u) ^ a * (rotationValue P u)⁻¹ ^ b = 1 ∨
      (rotationValue P u) ^ a * (rotationValue P u)⁻¹ ^ b = -1 := by
    rcases hsign with h | h
    · left
      have he := congrArg (fun Q : BPoly => Q.coeff (exponent a b)) h
      rw [coeff_rotate] at he
      apply mul_left_cancel₀ hc
      simpa [rotationValue] using he
    · right
      have he := congrArg (fun Q : BPoly => Q.coeff (exponent a b)) h
      rw [coeff_rotate, coeff_neg] at he
      apply mul_left_cancel₀ hc
      simpa [rotationValue] using he
  have hs : ((rotationValue P u) ^ a * (rotationValue P u)⁻¹ ^ b) ^ 2 = 1 := by
    rcases hchar with h | h <;> rw [h] <;> norm_num
  have hne : rotationValue P u ≠ 0 := u.val.ne_zero
  rw [mul_pow, inv_pow, ← pow_mul, ← inv_pow, ← pow_mul] at hs
  have he : (rotationValue P u) ^ (a * 2) = (rotationValue P u) ^ (b * 2) := by
    apply (div_eq_one_iff_eq (pow_ne_zero _ hne)).mp
    simpa [div_eq_mul_inv] using hs
  simpa [Nat.mul_comm] using he
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    Finite (centeredRotationGroup P) := by
  classical
  obtain ⟨a, b, hab, hc⟩ := exists_off_diagonal_coeff hP hinf hcircle
  let q : Polynomial ℂ := Polynomial.X ^ (2 * a) - Polynomial.X ^ (2 * b)
  have hq : q ≠ 0 := by
    intro h
    have he := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
    simp only [Polynomial.natDegree_X_pow] at he
    omega
  have hroots : ∀ u : centeredRotationGroup P, q.IsRoot (rotationValue P u) := by
    intro u
    simpa [q, Polynomial.IsRoot] using sub_eq_zero.mpr (rotation_value_root hP hinf hc u)
  let : Fintype {z : ℂ // q.IsRoot z} := (Polynomial.finite_setOfPred_isRoot hq).fintype
  exact Finite.of_injective (fun u => (⟨rotationValue P u, hroots u⟩ : {z : ℂ // q.IsRoot z}))
    (fun _ _ h => rotationValue_injective P (congrArg Subtype.val h))
end

#print axioms solution
