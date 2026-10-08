-- Prove2me | solution 1 for CurveSymmetry.family_point_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:57.209999+00:00
-- url     : https://prove2.me/submissions/e79d8381-3b34-4aa3-9960-19cfe2e57731

-- Solution generated from lean/FamilyRealLocus.lean (curve-symmetry-lean): inlined helpers in
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
lemma mul_star_eq_one_of_norm {a : ℂ} (ha : ‖a‖ = 1) : a * star a = 1 := by
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  change a * (starRingEnd ℂ) a = 1
  rw [← Complex.inv_eq_conj ha, mul_inv_cancel₀ hn]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma star_real_cast (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma mul_star_norm_sq (z : ℂ) : z * star z = (‖z‖ : ℂ) ^ 2 := by
  change z * (starRingEnd ℂ) z = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_familyPolynomial (m : ℕ) (α z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (familyPolynomial m α) =
      z ^ m * (α + z * star z) + star (z ^ m * (α + z * star z)) := by
  simp only [familyPolynomial, map_add, map_mul, map_pow, eval_C, eval_X,
    Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide,
    star_mul, star_pow, star_add, star_star]
  ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α)
    {r : ℝ} (hr : 0 ≤ r) : ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = r := by
  let b : ℂ := α + (r : ℂ) ^ 2
  have hb : b ≠ 0 := by
    intro h
    have hs := congrArg star h
    simp only [b, star_add, star_pow, star_real_cast, star_zero] at hs
    apply ha
    dsimp [b] at h
    linear_combination h - hs
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hnc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hnb
  let q : ℂ := Complex.I * star b / (‖b‖ : ℂ)
  have hq : ‖q‖ = 1 := by simp [q, hnb]
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq q hm
  have hvn : ‖v‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg v) hm.ne').mp
    rw [← norm_pow, hv, hq]
  have hvb : v ^ m * b = Complex.I * (‖b‖ : ℂ) := by
    rw [hv]
    dsimp [q]
    have he := mul_star_norm_sq b
    field_simp
    simp only [Complex.star_def] at he ⊢
    linear_combination he
  refine ⟨(r : ℂ) * v, ?_, by simp [hvn, abs_of_nonneg hr]⟩
  change eval _ (familyPolynomial m α) = 0
  rw [eval_familyPolynomial]
  have hz : ((r : ℂ) * v) * star ((r : ℂ) * v) = (r : ℂ) ^ 2 := by
    simp only [star_mul, star_real_cast]
    have he := mul_star_eq_one_of_norm hvn
    linear_combination (r : ℂ) ^ 2 * he
  have hw : ((r : ℂ) * v) ^ m * (α + ((r : ℂ) * v) * star ((r : ℂ) * v)) =
      (r : ℂ) ^ m * (Complex.I * (‖b‖ : ℂ)) := by
    rw [hz, mul_pow, mul_assoc]
    exact congrArg (fun x : ℂ => (r : ℂ) ^ m * x) hvb
  rw [hw]
  simp [star_mul, star_pow]
  ring
end

#print axioms solution
