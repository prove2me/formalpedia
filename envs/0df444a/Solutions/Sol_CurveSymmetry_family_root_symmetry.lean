-- Prove2me | solution 1 for CurveSymmetry.family_root_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:57.892141+00:00
-- url     : https://prove2.me/submissions/8d2bc23e-1249-46da-90da-00a7a7d83ac2

-- Solution generated from lean/FamilyRotations.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

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

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma family_rotate {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) (hroot : ζ ^ (2 * m) = 1) (α : ℂ) :
    rotate ζ (familyPolynomial m α) = C (ζ ^ m) * familyPolynomial m α := by
  have hs : ζ ^ m * ζ ^ m = 1 := by rw [← pow_add, ← two_mul]; exact hroot
  have hi : (ζ⁻¹) ^ m = ζ ^ m := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_left hs
  have h0 : rotate ζ (X 0) = C ζ * X 0 := by simp [rotate]
  have h1 : rotate ζ (X 1) = C (ζ⁻¹) * X 1 := by simp [rotate]
  have hC : ∀ c : ℂ, rotate ζ (C c) = C c := by intro c; simp [rotate]
  have hxy : (C ζ * X 0 : BPoly) * (C (ζ⁻¹) * X 1) = X 0 * X 1 := by
    have he : (C ζ : BPoly) * C (ζ⁻¹) = 1 := by rw [← C_mul, mul_inv_cancel₀ hζ, C_1]
    linear_combination (X 0 : BPoly) * X 1 * he
  simp only [familyPolynomial, map_add, map_mul, map_pow]
  rw [h0, h1, hC, hC, hxy, mul_pow, mul_pow, ← map_pow, ← map_pow, hi]
  ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hroot : ζ ^ (2 * m) = 1) (α : ℂ) : DirectSymmetry (realLocus (familyPolynomial m α)) ζ 0 := by
  have hζ : ζ ≠ 0 := by intro h; simp [h, hm.ne'] at hroot
  have hn : ‖ζ‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) (by omega : 2 * m ≠ 0)).mp
    have h := congrArg norm hroot
    simpa using h
  refine ⟨hn, ?_⟩
  intro z
  simp only [add_zero]
  change eval _ (familyPolynomial m α) = 0 ↔ eval _ (familyPolynomial m α) = 0
  rw [← eval_rotate ζ hn, family_rotate hζ hroot α, map_mul, eval_C]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hζ))
end

#print axioms solution
