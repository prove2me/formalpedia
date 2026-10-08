-- Prove2me | solution 1 for CurveSymmetry.polynomial_rotation_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:42.295986+00:00
-- url     : https://prove2.me/submissions/45b9cfbf-e21d-4f79-a2a2-cdb46dac757f

-- Solution generated from lean/RotationSupport.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_anti_even_order
import Theorems.Thm_CurveSymmetry_anti_support
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
/-- The degree gap in the rotation bound, without any geometric hypotheses. -/
theorem anti_degree_gap {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    (hnot : ¬ P.IsHomogeneous m) : m + 2 ≤ P.totalDegree := by
  by_contra hgap
  apply hnot
  intro s hs
  have hd := support_degree (mem_support_iff.mpr hs)
  have hw := anti_support hm hζ hdeg hanti (mem_support_iff.mpr hs)
  have he : s 0 + s 1 = m := by omega
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
  exact (exponent_degree s).trans he
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A polynomial fixed by a rotation of order greater than its degree is radial. -/
theorem fixed_support {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {P : BPoly}
    (hdeg : P.totalDegree < N) (hfixed : rotate ζ P = P)
    {s : Exponent} (hs : s ∈ P.support) : s 0 = s 1 := by
  have hc : P.coeff s ≠ 0 := mem_support_iff.mp hs
  have hd := support_degree hs
  have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
  have heq := congrArg (fun Q : BPoly => Q.coeff s) hfixed
  rw [coeff_rotate] at heq
  have hchar : ζ ^ s 0 * (ζ⁻¹) ^ s 1 = 1 := by
    apply mul_left_cancel₀ hc
    simpa using heq
  rw [inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hz)] at hchar
  exact hζ.pow_inj (by omega) (by omega) hchar
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {P : BPoly} (hd : 2 ≤ P.totalDegree)
    (hnonradial : ∃ s ∈ P.support, s 0 ≠ s 1)
    (hhom : ∀ m : ℕ, 2 ≤ m → ¬ P.IsHomogeneous m)
    (hsign : rotate ζ P = P ∨ rotate ζ P = -P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  by_cases hsmall : N ≤ P.totalDegree
  · exact le_trans hsmall (le_max_left _ _)
  have hlarge : P.totalDegree < N := by omega
  rcases hsign with hfixed | hanti
  · obtain ⟨s, hs, hne⟩ := hnonradial
    exact (hne (fixed_support hζ hlarge hfixed hs)).elim
  · have hP : P ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨m, hN⟩ := anti_even_order hζ hP hanti
    have horder : N = 2 * m := by omega
    have hm : 2 ≤ m := by omega
    have hgap := anti_degree_gap (by omega) (horder ▸ hζ)
      (by omega) hanti (hhom m hm)
    exact le_trans (by omega : N ≤ 2 * P.totalDegree - 4) (le_max_right _ _)
end

#print axioms solution
