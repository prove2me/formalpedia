-- Prove2me | solution 1 for CurveSymmetry.family_dilation_parameter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:27.29615+00:00
-- url     : https://prove2.me/submissions/e90bbe95-0f4c-4301-8818-a529e4cf0a5c

-- Solution generated from lean/FamilyTransport.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_fourTermForm_proportional_iff
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
lemma family_fourTerm (m : ℕ) (α : ℂ) :
    familyPolynomial m α = fourTermForm m α (star α) 1 1 := by
  simp only [familyPolynomial, fourTermForm, binaryForm, map_one, one_mul]
  ring
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
open MvPolynomial
lemma norm_one_of_mul_star_norm_one {c : ℂ} (h : ‖c * star c‖ = 1) : ‖c‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by decide : 2 ≠ 0)).mp
  simpa [norm_mul, norm_star, pow_two] using h
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {α β c k : ℂ}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hc : c ≠ 0)
    (he : dilate c (familyPolynomial m β) = C k * familyPolynomial m α) :
    ‖c‖ = 1 ∧ β = α := by
  rw [dilate_family_fourTerm, family_fourTerm] at he
  obtain ⟨hlow, _, hhigh, _⟩ :=
    (fourTermForm_proportional_iff hm _ _ _ _ _ _ _ _ _).mp he
  rw [mul_one] at hhigh
  have hp : β = (c * star c) * α := by
    apply mul_left_cancel₀ (pow_ne_zero m hc)
    rw [hlow, ← hhigh]
    ring
  have hn := congrArg norm hp
  rw [hβ, norm_mul, hα, mul_one] at hn
  have hcn := norm_one_of_mul_star_norm_one hn.symm
  rw [mul_star_eq_one_of_norm hcn, one_mul] at hp
  exact ⟨hcn, hp⟩
end

#print axioms solution
