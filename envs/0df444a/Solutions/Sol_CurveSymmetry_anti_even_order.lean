-- Prove2me | solution 1 for CurveSymmetry.anti_even_order
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:25.073766+00:00
-- url     : https://prove2.me/submissions/f3055036-7bb3-4e3c-affe-c1be300197cd

-- Solution generated from lean/RotationSupport.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {P : BPoly}
    (hP : P ≠ 0) (hanti : rotate ζ P = -P) : Even N := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
  have heq := congrArg (fun Q : BPoly => Q.coeff s) hanti
  rw [coeff_rotate, coeff_neg] at heq
  have hchar : ζ ^ s 0 * (ζ⁻¹) ^ s 1 = -1 := by
    apply mul_left_cancel₀ hs
    simpa using heq
  have hpow : (-1 : ℂ) ^ N = 1 := by
    rw [← hchar, mul_pow, ← pow_mul, Nat.mul_comm (s 0) N, pow_mul, hζ.pow_eq_one]
    rw [← pow_mul, Nat.mul_comm (s 1) N, pow_mul, inv_pow, hζ.pow_eq_one]
    simp
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp hpow
end

#print axioms solution
