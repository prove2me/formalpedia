-- Prove2me | solution 1 for CurveSymmetry.normalize_twoParameter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:16.71465+00:00
-- url     : https://prove2.me/submissions/4a5b3cc2-513b-4583-8d35-7b8088ff7cc3

-- Solution generated from lean/Normalization.lean (curve-symmetry-lean): inlined helpers in
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
lemma dilate_twoParameter (m : ℕ) (a b c : ℂ) :
    dilate c (twoParameter m a b) =
      twoParameter m (c ^ m * a) (c ^ m * b * (c * star c)) := by
  simp only [twoParameter, map_add, map_mul, map_pow]
  have h0 : dilate c (X 0) = C c * X 0 := by simp [dilate]
  have h1 : dilate c (X 1) = C (star c) * X 1 := by simp [dilate]
  have hC : ∀ a : ℂ, dilate c (C a) = C a := by intro a; simp [dilate]
  rw [h0, h1, hC, hC, hC, hC]
  simp only [star_mul, star_pow, star_star, map_mul, map_pow, mul_pow]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma twoParameter_real_scalar (m : ℕ) (α : ℂ) (k : ℝ) :
    twoParameter m ((k : ℂ) * α) (k : ℂ) = C (k : ℂ) * familyPolynomial m α := by
  simp only [twoParameter, familyPolynomial, star_mul, star_real_cast, map_mul]
  ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (hb : b ≠ 0) (hreal : a / b ≠ star (a / b)) :
    ∃ c α : ℂ, ∃ k : ℝ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧ 0 < k ∧
      dilate c (twoParameter m a b) = C (k : ℂ) * familyPolynomial m α := by
  let q : ℂ := a / b
  have hq : q ≠ 0 := by intro h; apply hreal; change q = star q; simp [h]
  have hnq : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hncq : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast hnq
  let r : ℝ := Real.sqrt ‖q‖
  have hr : 0 < r := Real.sqrt_pos.mpr (norm_pos_iff.mpr hq)
  have hrs : r ^ 2 = ‖q‖ := Real.sq_sqrt (norm_nonneg q)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ((‖b‖ : ℂ) / b) hm
  have hun : ‖u‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg u) hm.ne').mp
    have he := congrArg norm hu
    simpa [hnb] using he
  have hu0 : u ≠ 0 := by intro h; simp [h] at hun
  let c : ℂ := (r : ℂ) * u
  let α : ℂ := q / (‖q‖ : ℂ)
  let k : ℝ := r ^ m * ‖b‖ * ‖q‖
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') hu0
  have hαn : ‖α‖ = 1 := by simp [α, hnq]
  have hαr : α ≠ star α := by
    intro h
    have he : (‖q‖ : ℂ) * α = q := mul_div_cancel₀ _ hncq
    have hs := congrArg star he
    simp only [star_mul, star_real_cast, ← h] at hs
    apply hreal
    change q = star q
    linear_combination hs - he
  have hk : 0 < k := by dsimp [k]; positivity
  have hcc : c * star c = (‖q‖ : ℂ) := by
    have he := mul_star_eq_one_of_norm hun
    have hrs' : (r : ℂ) ^ 2 = (‖q‖ : ℂ) := by exact_mod_cast hrs
    change ((r : ℂ) * u) * star ((r : ℂ) * u) = (‖q‖ : ℂ)
    simp only [star_mul, star_real_cast]
    linear_combination (r : ℂ) ^ 2 * he + hrs'
  have hcb : c ^ m * b = (r : ℂ) ^ m * (‖b‖ : ℂ) := by
    dsimp [c]
    rw [mul_pow, hu]
    field_simp
  have hA : c ^ m * a = (k : ℂ) * α := by
    calc
      c ^ m * a = (c ^ m * b) * q := by dsimp [q]; field_simp
      _ = ((r : ℂ) ^ m * (‖b‖ : ℂ)) * q := by rw [hcb]
      _ = (k : ℂ) * α := by dsimp [k, α]; push_cast; field_simp
  have hB : c ^ m * b * (c * star c) = (k : ℂ) := by
    rw [hcb, hcc]
    simp [k]
  refine ⟨c, α, k, hc, hαn, hαr, hk, ?_⟩
  rw [dilate_twoParameter, hA, hB, twoParameter_real_scalar]
end

#print axioms solution
