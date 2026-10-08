-- Prove2me | solution 1 for CurveSymmetry.anti_radial_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:25.142468+00:00
-- url     : https://prove2.me/submissions/ca0f4514-78f9-44fe-bcee-a33a688ec885

-- Solution generated from lean/RadialAntiForm.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Theorems.Thm_CurveSymmetry_anti_support
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
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
lemma weightPolynomial_coeff (P : BPoly) (m k : ℕ) :
    (weightPolynomial P m).coeff k = P.coeff (exponent (k + m) k) := by
  classical
  simp only [weightPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (Finset.mem_image.mpr ⟨exponent (k + m) k, mem_support_iff.mpr (Ne.symm hc), by simp⟩)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma oppositeWeightPolynomial_coeff (P : BPoly) (m k : ℕ) :
    (oppositeWeightPolynomial P m).coeff k = P.coeff (exponent k (k + m)) := by
  classical
  simp only [oppositeWeightPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (Finset.mem_image.mpr ⟨exponent k (k + m), mem_support_iff.mpr (Ne.symm hc), by simp⟩)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma X_pow_mul_aeval (m : ℕ) (A : Polynomial ℂ) :
    (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A =
      ∑ k ∈ A.support, monomial (exponent (k + m) k) (A.coeff k) := by
  conv_lhs => rw [A.as_sum_support, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.aeval_monomial, monomial_exponent, MvPolynomial.algebraMap_eq]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma Y_pow_mul_aeval (m : ℕ) (A : Polynomial ℂ) :
    (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A =
      ∑ k ∈ A.support, monomial (exponent k (k + m)) (A.coeff k) := by
  conv_lhs => rw [A.as_sum_support, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.aeval_monomial, monomial_exponent, MvPolynomial.algebraMap_eq]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma coeff_sum_weight (A : Polynomial ℂ) (m : ℕ) (s : Exponent) :
    (∑ k ∈ A.support, monomial (exponent (k + m) k) (A.coeff k)).coeff s =
      if s 0 = s 1 + m then A.coeff (s 1) else 0 := by
  classical
  have hc : ∀ k, (exponent (k + m) k = s) ↔ (s 0 = s 1 + m ∧ k = s 1) := by
    intro k
    rw [eq_comm, exponent_eq_iff]
    constructor <;> intro h <;> omega
  simp only [coeff_sum, coeff_monomial, hc]
  by_cases h : s 0 = s 1 + m
  · rw [if_pos h]
    simp only [h, true_and, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · exact (Polynomial.notMem_support_iff.mp hmem).symm
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun k _ => by simp [h]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma coeff_sum_opposite_weight (A : Polynomial ℂ) (m : ℕ) (s : Exponent) :
    (∑ k ∈ A.support, monomial (exponent k (k + m)) (A.coeff k)).coeff s =
      if s 1 = s 0 + m then A.coeff (s 0) else 0 := by
  classical
  have hc : ∀ k, (exponent k (k + m) = s) ↔ (s 1 = s 0 + m ∧ k = s 0) := by
    intro k
    rw [eq_comm, exponent_eq_iff]
    constructor <;> intro h <;> omega
  simp only [coeff_sum, coeff_monomial, hc]
  by_cases h : s 1 = s 0 + m
  · rw [if_pos h]
    simp only [h, true_and, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · exact (Polynomial.notMem_support_iff.mp hmem).symm
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun k _ => by simp [h]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * m))
    {P : BPoly} (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P) :
    P = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (weightPolynomial P m) +
        (X 1 : BPoly) ^ m *
          Polynomial.aeval ((X 0 : BPoly) * X 1) (oppositeWeightPolynomial P m) ∧
      (weightPolynomial P m).natDegree ≤ (P.totalDegree - m) / 2 ∧
      (oppositeWeightPolynomial P m).natDegree ≤ (P.totalDegree - m) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [X_pow_mul_aeval, Y_pow_mul_aeval]
    ext s
    rw [MvPolynomial.coeff_add, coeff_sum_weight, coeff_sum_opposite_weight, weightPolynomial_coeff,
      oppositeWeightPolynomial_coeff]
    by_cases hs : s ∈ P.support
    · rcases anti_support hm hζ hdeg hanti hs with h | h
      · rw [if_pos h, if_neg (by omega), add_zero, ← exponent_eq_iff.mpr ⟨h, rfl⟩]
      · rw [if_neg (by omega), if_pos h, zero_add, ← exponent_eq_iff.mpr ⟨rfl, h⟩]
    · have hc := notMem_support_iff.mp hs
      rw [hc]
      split_ifs with h1 h2 h2
      · omega
      · rw [← exponent_eq_iff.mpr ⟨h1, rfl⟩, hc, add_zero]
      · rw [← exponent_eq_iff.mpr ⟨rfl, h2⟩, hc, zero_add]
      · simp
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [weightPolynomial_coeff]
    by_contra hc
    have hd := support_degree (mem_support_iff.mpr hc)
    simp only [exponent_zero, exponent_one] at hd
    omega
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [oppositeWeightPolynomial_coeff]
    by_contra hc
    have hd := support_degree (mem_support_iff.mpr hc)
    simp only [exponent_zero, exponent_one] at hd
    omega
end

#print axioms solution
