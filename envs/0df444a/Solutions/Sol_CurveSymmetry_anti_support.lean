-- Prove2me | solution 1 for CurveSymmetry.anti_support
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:25.729433+00:00
-- url     : https://prove2.me/submissions/f6dc1079-7841-4dc3-86a6-f16891fcf1ff

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

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma primitive_half_turn {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) : ζ ^ m = -1 := by
  have hs : (ζ ^ m) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 2]
    exact hζ.pow_eq_one
  rcases (sq_eq_one_iff).mp hs with h | h
  · exact (hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega) h).elim
  · exact h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Below degree `2m`, an anti-invariant monomial has weight `m` or `-m`. -/
theorem anti_weight {m a b : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) (hdeg : a + b < 2 * m)
    (hanti : ζ ^ a * (ζ⁻¹) ^ b = -1) : a = b + m ∨ b = a + m := by
  have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hhalf := primitive_half_turn hm hζ
  have hp : ζ ^ a = -(ζ ^ b) := by
    rw [inv_pow, ← div_eq_mul_inv] at hanti
    simpa using (div_eq_iff (pow_ne_zero b hz)).mp hanti
  by_cases hb : b < m
  · left
    apply hζ.pow_inj (by omega) (by omega)
    simpa [pow_add, hhalf] using hp
  · right
    apply hζ.pow_inj (by omega) (by omega)
    simp [pow_add, hhalf, hp]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    {s : Exponent} (hs : s ∈ P.support) : s 0 = s 1 + m ∨ s 1 = s 0 + m := by
  have hc : P.coeff s ≠ 0 := mem_support_iff.mp hs
  have heq := congrArg (fun Q : BPoly => Q.coeff s) hanti
  rw [coeff_rotate, coeff_neg] at heq
  have hchar : ζ ^ s 0 * (ζ⁻¹) ^ s 1 = -1 := by
    apply mul_left_cancel₀ hc
    simpa using heq
  exact anti_weight hm hζ (lt_of_le_of_lt (support_degree hs) hdeg) hchar
end

#print axioms solution
